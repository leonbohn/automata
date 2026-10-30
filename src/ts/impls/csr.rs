use std::borrow::Cow;

use crate::{
    Color, TransitionSystem, Void,
    alphabet::{CharAlphabet, IndexedAlphabet},
    math,
    ts::{
        DefaultIdType, Deterministic, EdgeId, EdgeOf, EdgeRef, StateIndex, States, SymbolOf,
        predecessors::PredecessorIterable,
    },
};

/// The sentinel that stands for "no edge" in the target slots of [`CsrTs`].
pub(super) const NONE: DefaultIdType = DefaultIdType::MAX;

/// A deterministic transition system over an [`IndexedAlphabet`] that cannot be changed after it
/// has been built, and keeps everything in a few flat vectors.
///
/// # Layout
/// Like [`DenseTs`](crate::ts::DenseTs), the edge leaving state `q` on the symbol with index `a` is
/// in slot `q * k + a` of a table (and has this slot as its [`EdgeId`]), so a lookup is one index
/// computation and a load. The incoming edges are stored in compressed sparse row form: the slots
/// that lead to a state are listed in increasing order, see `ReverseCsr`.
/// Compared to the growable storages there are no tombstones, no links and one allocation per
/// vector instead of one per state.
///
/// A system is built with [`CsrTs::from_ts`] or by the [`Csr`](crate::ts::Csr) storage. State
/// indices are consecutive, starting at 0, in the order of the system it was built from.
#[derive(Clone)]
pub struct CsrTs<A: IndexedAlphabet = CharAlphabet, Q = Void, C = Void> {
    alphabet: A,
    states: Vec<Q>,
    targets: Vec<DefaultIdType>,
    colors: Vec<Option<C>>,
    incoming: ReverseCsr,
}

/// The incoming edges of the states of a deterministic table in compressed sparse row form: the
/// slots that lead to state `p` are `slots[offsets[p]..offsets[p + 1]]`, in increasing order.
#[derive(Clone, Debug)]
pub(super) struct ReverseCsr {
    offsets: Vec<DefaultIdType>,
    slots: Vec<DefaultIdType>,
}

impl ReverseCsr {
    /// Collects the slots of the `n` states whose targets are given, where `NONE` marks an empty
    /// slot, in O(number of slots).
    pub(super) fn build(targets: &[DefaultIdType], n: usize) -> Self {
        let mut offsets = vec![0 as DefaultIdType; n + 1];
        for target in targets.iter().filter(|t| **t != NONE) {
            offsets[*target as usize + 1] += 1;
        }
        for p in 0..n {
            offsets[p + 1] += offsets[p];
        }
        let mut fill = offsets.clone();
        let mut slots = vec![NONE; offsets[n] as usize];
        for (slot, target) in targets.iter().enumerate() {
            if *target != NONE {
                slots[fill[*target as usize] as usize] = slot as DefaultIdType;
                fill[*target as usize] += 1;
            }
        }
        Self { offsets, slots }
    }

    /// The slots that lead to state `p`.
    #[inline]
    pub(super) fn to_state(&self, p: usize) -> &[DefaultIdType] {
        &self.slots[self.offsets[p] as usize..self.offsets[p + 1] as usize]
    }

    /// Panics unless this is the table of the given targets. If `stale` is set, it may also list
    /// slots that no longer lead to the state, as left behind by removing edges.
    pub(super) fn check_against(&self, targets: &[DefaultIdType], n: usize, stale: bool) {
        assert_eq!(self.offsets.len(), n + 1, "wrong number of offsets");
        for p in 0..n {
            let expected: Vec<_> = (0..targets.len())
                .filter(|slot| targets[*slot] as usize == p)
                .map(|slot| slot as DefaultIdType)
                .collect();
            let listed: Vec<_> = self
                .to_state(p)
                .iter()
                .copied()
                .filter(|slot| !stale || targets[*slot as usize] as usize == p)
                .collect();
            assert_eq!(listed, expected, "wrong incoming edges of state {p}");
        }
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> CsrTs<A, Q, C> {
    /// Builds a system with the states and the edges of the deterministic system `ts`. The states
    /// are numbered in the order in which [`States::states`] yields them.
    ///
    /// # Panics
    /// Panics if there are too many states or edge slots for 32 bit ids.
    pub fn from_ts<T>(ts: &T) -> Self
    where
        T: Deterministic + States<Alphabet = A, StateColor = Q, EdgeColor = C>,
    {
        let alphabet = ts.alphabet().clone();
        let k = alphabet.size();
        let renaming: math::FxIndexMap<T::StateIndex, DefaultIdType> = ts
            .states()
            .enumerate()
            .map(|(i, q)| (q, i as DefaultIdType))
            .collect();
        let n = renaming.len();
        DefaultIdType::try_from(n * k)
            .ok()
            .filter(|slots| *slots != NONE)
            .expect("too many edge slots for 32 bit ids");

        let mut states = Vec::with_capacity(n);
        let mut targets = vec![NONE; n * k];
        let mut colors = vec![None; n * k];
        for (q, i) in renaming.iter() {
            states.push(ts.state_color(*q).expect("state exists").into_owned());
            for edge in ts.edges_from(*q).expect("state exists") {
                let slot = *i as usize * k + alphabet.expression_to_index(edge.expression());
                let target = renaming[&edge.target()];
                targets[slot] = target;
                colors[slot] = Some(edge.color().clone());
            }
        }

        let incoming = ReverseCsr::build(&targets, n);
        Self {
            alphabet,
            states,
            targets,
            colors,
            incoming,
        }
    }

    /// The edge in slot `slot` leaving `source` on the symbol with index `symbol_index`, if there
    /// is one.
    #[inline(always)]
    fn edge_in_slot(
        &self,
        source: DefaultIdType,
        slot: usize,
        symbol_index: usize,
    ) -> Option<EdgeOf<'_, Self>> {
        let target = self.targets[slot];
        if target == NONE {
            return None;
        }
        Some(
            EdgeRef::borrowed(
                source,
                self.alphabet.expression_ref(symbol_index),
                self.colors[slot].as_ref().expect("edge has a color"),
                target,
            )
            .with_id(EdgeId(slot as u32)),
        )
    }

    /// Checks the invariants of the data structure and panics if one is violated: the sizes of
    /// the vectors, that a slot has a color exactly if it has a target, that all targets exist,
    /// and that the incoming slots of every state are those that lead to it, in increasing order.
    pub fn check_consistency(&self) {
        let k = self.alphabet.size();
        let n = self.states.len();
        assert_eq!(self.targets.len(), n * k, "wrong number of target slots");
        assert_eq!(self.colors.len(), n * k, "wrong number of color slots");
        for (slot, target) in self.targets.iter().enumerate() {
            assert_eq!(
                self.colors[slot].is_some(),
                *target != NONE,
                "slot {slot} has a color iff it has a target"
            );
            assert!(
                *target == NONE || (*target as usize) < n,
                "edge {slot} leads to a state that does not exist"
            );
        }
        self.incoming.check_against(&self.targets, n, false);
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> TransitionSystem for CsrTs<A, Q, C> {
    type Alphabet = A;
    type StateIndex = DefaultIdType;
    type StateColor = Q;
    type EdgeColor = C;
    type EdgesFromIter<'this>
        = CsrEdgesFrom<'this, A, Q, C>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        let q = state as usize;
        if q >= self.states.len() {
            return None;
        }
        Some(CsrEdgesFrom::new(self, state))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.states.get(state as usize).map(Cow::Borrowed)
    }

    fn state_bound(&self) -> Option<usize> {
        Some(self.states.len())
    }
}

/// Iterates over the edges that leave a state of a [`CsrTs`], in the order of the alphabet.
pub struct CsrEdgesFrom<'ts, A: IndexedAlphabet, Q, C> {
    alphabet: &'ts A,
    source: DefaultIdType,
    /// The slot of the next edge to look at.
    slot: usize,
    /// The index of the symbol of the next edge to look at.
    symbol_index: usize,
    targets: std::slice::Iter<'ts, DefaultIdType>,
    colors: std::slice::Iter<'ts, Option<C>>,
    _ts: std::marker::PhantomData<fn() -> Q>,
}

impl<'ts, A: IndexedAlphabet, Q, C> CsrEdgesFrom<'ts, A, Q, C> {
    #[inline(always)]
    fn new(ts: &'ts CsrTs<A, Q, C>, state: DefaultIdType) -> Self {
        let k = ts.alphabet.size();
        let slots = state as usize * k..(state as usize + 1) * k;
        Self {
            alphabet: &ts.alphabet,
            source: state,
            slot: slots.start,
            symbol_index: 0,
            targets: ts.targets[slots.clone()].iter(),
            colors: ts.colors[slots].iter(),
            _ts: std::marker::PhantomData,
        }
    }
}

impl<'ts, A: IndexedAlphabet, Q: Color, C: Color> Iterator for CsrEdgesFrom<'ts, A, Q, C> {
    type Item = EdgeOf<'ts, CsrTs<A, Q, C>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        for (&target, color) in self.targets.by_ref().zip(self.colors.by_ref()) {
            let (slot, symbol_index) = (self.slot, self.symbol_index);
            self.slot += 1;
            self.symbol_index += 1;
            if target != NONE {
                let color = color.as_ref().expect("edge has a color");
                return Some(
                    EdgeRef::borrowed(
                        self.source,
                        self.alphabet.expression_ref(symbol_index),
                        color,
                        target,
                    )
                    .with_id(EdgeId(slot as u32)),
                );
            }
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.targets.len()))
    }

    #[inline]
    fn count(self) -> usize {
        self.targets.filter(|t| **t != NONE).count()
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> States for CsrTs<A, Q, C> {
    type StatesIter<'this>
        = std::ops::Range<DefaultIdType>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        0..self.states.len() as DefaultIdType
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        (index as usize) < self.states.len()
    }

    fn state_count(&self) -> usize {
        self.states.len()
    }

    /// Checks that no slot is empty, which takes O(n * k) time.
    fn is_complete(&self) -> bool {
        self.targets.iter().all(|t| *t != NONE)
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> Deterministic for CsrTs<A, Q, C> {
    #[inline]
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        let index = self.alphabet.try_symbol_to_index(symbol)?;
        let slot = state as usize * self.alphabet.size() + index;
        if slot >= self.targets.len() {
            return None;
        }
        self.edge_in_slot(state, slot, index)
    }

    #[inline]
    fn successor(
        &self,
        state: StateIndex<Self>,
        symbol: SymbolOf<Self>,
    ) -> Option<StateIndex<Self>> {
        let index = self.alphabet.try_symbol_to_index(symbol)?;
        let slot = state as usize * self.alphabet.size() + index;
        self.targets.get(slot).copied().filter(|t| *t != NONE)
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> PredecessorIterable for CsrTs<A, Q, C> {
    type EdgesToIter<'this>
        = CsrEdgesTo<'this, A, Q, C>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        let p = state as usize;
        (p < self.states.len()).then(|| CsrEdgesTo {
            ts: self,
            slots: self.incoming.to_state(p).iter(),
        })
    }
}

/// Iterates over the edges that enter a state of a [`CsrTs`], ordered by their slot.
pub struct CsrEdgesTo<'ts, A: IndexedAlphabet, Q, C> {
    ts: &'ts CsrTs<A, Q, C>,
    slots: std::slice::Iter<'ts, DefaultIdType>,
}

impl<'ts, A: IndexedAlphabet, Q: Color, C: Color> Iterator for CsrEdgesTo<'ts, A, Q, C> {
    type Item = EdgeOf<'ts, CsrTs<A, Q, C>>;

    fn next(&mut self) -> Option<Self::Item> {
        let slot = *self.slots.next()? as usize;
        let k = self.ts.alphabet.size();
        Some(
            self.ts
                .edge_in_slot((slot / k) as DefaultIdType, slot, slot % k)
                .expect("listed edge exists"),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::{Csr, DenseTs, ForAlphabet, LinkedTs, Shrinkable, Sproutable, Storage};

    fn dense() -> DenseTs<CharAlphabet, bool, u32> {
        let mut ts = DenseTs::for_alphabet(CharAlphabet::of_size(2));
        let q: Vec<_> = (0..4).map(|i| ts.add_state(i % 2 == 0)).collect();
        ts.add_edge((q[0], 'a', 1u32, q[1]));
        ts.add_edge((q[1], 'a', 2u32, q[2]));
        ts.add_edge((q[2], 'a', 3u32, q[0]));
        ts.add_edge((q[0], 'b', 4u32, q[0]));
        ts.add_edge((q[3], 'b', 5u32, q[0]));
        ts
    }

    #[test]
    fn lookups_and_predecessors() {
        let ts = CsrTs::from_ts(&dense());
        ts.check_consistency();
        assert_eq!(ts.state_count(), 4);
        assert_eq!(ts.successor(0, 'a'), Some(1));
        assert_eq!(ts.successor(0, 'b'), Some(0));
        assert_eq!(ts.successor(1, 'b'), None);
        assert_eq!(ts.successor(0, 'z'), None);
        assert_eq!(ts.successor(9, 'a'), None);
        assert_eq!(ts.edge(2, 'a').unwrap().id(), Some(EdgeId(4)));
        assert!(*ts.state_color(2).unwrap());
        assert!(ts.edges_from(9).is_none() && ts.predecessors(9).is_none());
        // incoming edges of 0, ordered by slot: (0, b), (2, a), (3, b)
        let into_zero: Vec<_> = ts
            .predecessors(0)
            .unwrap()
            .map(|e| (e.source(), *e.expression(), *e.color()))
            .collect();
        assert_eq!(into_zero, vec![(0, 'b', 4), (2, 'a', 3), (3, 'b', 5)]);
        assert!(!ts.is_complete());
    }

    #[test]
    fn removed_states_are_dropped_and_the_rest_renumbered() {
        let mut source = dense();
        source.remove_state(1);
        let ts = CsrTs::from_ts(&source);
        ts.check_consistency();
        assert_eq!(ts.state_count(), 3);
        // the old states 0, 2, 3 are now 0, 1, 2
        assert_eq!(ts.successor(1, 'a'), Some(0));
        assert_eq!(ts.successor(2, 'b'), Some(0));
        assert_eq!(ts.successor(0, 'a'), None);
    }

    #[test]
    fn empty_system() {
        let ts = CsrTs::from_ts(&DenseTs::<CharAlphabet, bool, u32>::for_alphabet(
            CharAlphabet::of_size(2),
        ));
        ts.check_consistency();
        assert_eq!(ts.state_count(), 0);
        assert!(ts.is_complete());
    }

    #[test]
    fn storage_converts_deterministic_linked() {
        let mut linked = LinkedTs::for_alphabet(CharAlphabet::of_size(2));
        let (q0, q1) = (linked.add_state(true), linked.add_state(false));
        linked.add_edge((q0, 'a', Void, q1));
        let csr = <Csr as Storage<_>>::try_from_linked(linked.clone()).unwrap();
        assert_eq!(csr.successor(0, 'a'), Some(1));

        linked.add_edge((q0, 'a', Void, q0));
        assert!(<Csr as Storage<_>>::try_from_linked(linked).is_err());
    }
}
