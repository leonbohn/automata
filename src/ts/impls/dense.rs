use std::{borrow::Cow, sync::OnceLock};

use crate::representation::{FromTransitions, IntoTransitions, Parts, sprout_from_parts};
use crate::{
    Color, TransitionSystem, Void,
    alphabet::{CharAlphabet, IndexedAlphabet},
    ts::{
        Dense, DenseId, Deterministic, EdgeColor, EdgeId, EdgeOf, EdgeRef, EdgeTuple, ForAlphabet,
        IdType, IntoEdgeTuple, Shrinkable, Sproutable, StateColor, StateId, StateIndex, States,
        SymbolOf, predecessors::PredecessorIterable,
    },
};

/// The sentinel that stands for "no edge" in the target slots of [`DenseTs`].
pub(super) const NONE: u32 = u32::MAX;

/// The incoming edges of the states of a deterministic table in compressed sparse row form: the
/// slots that lead to state `p` are `slots[offsets[p]..offsets[p + 1]]`, in increasing order.
#[derive(Clone, Debug)]
pub(super) struct ReverseCsr {
    offsets: Vec<u32>,
    slots: Vec<u32>,
}

impl ReverseCsr {
    /// Collects the slots of the `n` states whose targets are given, where `NONE` marks an empty
    /// slot, in O(number of slots).
    pub(super) fn build(targets: &[u32], n: usize) -> Self {
        let mut offsets = vec![0_u32; n + 1];
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
                slots[fill[*target as usize] as usize] = slot as u32;
                fill[*target as usize] += 1;
            }
        }
        Self { offsets, slots }
    }

    /// The slots that lead to state `p`.
    #[inline]
    pub(super) fn to_state(&self, p: usize) -> &[u32] {
        &self.slots[self.offsets[p] as usize..self.offsets[p + 1] as usize]
    }

    /// Panics unless this is the table of the given targets. If `stale` is set, it may also list
    /// slots that no longer lead to the state, as left behind by removing edges.
    pub(super) fn check_against(&self, targets: &[u32], n: usize, stale: bool) {
        assert_eq!(self.offsets.len(), n + 1, "wrong number of offsets");
        for p in 0..n {
            let expected: Vec<_> = (0..targets.len())
                .filter(|slot| targets[*slot] as usize == p)
                .map(|slot| slot as u32)
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

/// A deterministic transition system over an [`IndexedAlphabet`] that stores the transitions in a
/// table with one slot per state and symbol.
///
/// # Layout
/// For `n` states and an alphabet of size `k`, the edge leaving state `q` on the symbol with
/// index `a` lives in slot `q * k + a`, which is also its [`EdgeId`]. Looking up an edge is thus one
/// index computation and a load. The targets and colors of the slots are kept in two separate
/// vectors, a target of `NONE` marks an absent edge.
///
/// No expression is stored per edge, it is lent out by the alphabet via
/// [`IndexedAlphabet::expression_ref`].
///
/// The incoming edges of a state are not maintained while the system is changed. They are collected
/// into a reverse compressed sparse row table the first time [`PredecessorIterable::predecessors`]
/// is called, in O(n * k). Adding a state or an edge drops the table. Removing edges keeps it, it
/// then lists slots that no longer lead to the state, which readers skip. Changing the system is
/// thus as cheap as it can be, and a system that is built first and queried afterwards pays for the
/// table once.
///
/// A removed state is a tombstone (`None` in `states`), so that the indices of all other states stay
/// valid.
///
/// Inserting an edge overwrites the slot of its source and symbol, so the id of the new edge is the
/// id of the replaced one.
#[derive(Clone)]
pub struct DenseTs<A: IndexedAlphabet = CharAlphabet, Q = Void, C = Void> {
    alphabet: A,
    states: Vec<Option<Q>>,
    targets: Vec<u32>,
    colors: Vec<Option<C>>,
    /// The incoming edges, built on demand and dropped when edges or states are added. After
    /// removals it is a superset of the incoming edges.
    incoming: OnceLock<ReverseCsr>,
}

impl<A: IndexedAlphabet, Q: Color, C: Color> DenseTs<A, Q, C> {
    /// Builds a new empty transition system for the given alphabet.
    pub fn new(alphabet: A) -> Self {
        Self::with_capacity(alphabet, 0)
    }

    /// Builds a new empty transition system for the given alphabet with room for `cap` states.
    pub fn with_capacity(alphabet: A, cap: usize) -> Self {
        let k = alphabet.size();
        Self {
            states: Vec::with_capacity(cap),
            targets: Vec::with_capacity(cap * k),
            colors: Vec::with_capacity(cap * k),
            incoming: OnceLock::new(),
            alphabet,
        }
    }

    /// The id of the slot for the edge leaving `state` on the symbol with the given index.
    #[inline(always)]
    fn slot(&self, state: usize, symbol_index: usize) -> usize {
        state * self.alphabet.size() + symbol_index
    }

    /// The range of the slots that belong to `state`.
    #[inline(always)]
    fn slots_of(&self, state: usize) -> std::ops::Range<usize> {
        let k = self.alphabet.size();
        state * k..(state + 1) * k
    }

    /// Whether `state` is the index of a state that has not been removed.
    #[inline(always)]
    fn is_live(&self, state: usize) -> bool {
        self.states.get(state).is_some_and(Option::is_some)
    }

    /// The edge in slot `slot` leaving `source` on the symbol with index `symbol_index`, if there
    /// is one.
    #[inline(always)]
    fn edge_in_slot(
        &self,
        source: StateId,
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
                StateId::from(target),
            )
            .with_id(EdgeId(slot as u32)),
        )
    }

    /// Checks the invariants of the data structure and panics if one is violated:
    /// - there is one slot per state and symbol,
    /// - a slot has a color exactly if it has a target,
    /// - the source and the target of every edge are live states,
    /// - if the incoming edges have been collected, they are those that lead to each state.
    ///
    /// # Panics
    /// Panics if one of the invariants is violated.
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
            if *target == NONE {
                continue;
            }
            assert!(self.is_live(slot / k), "edge {slot} leaves a removed state");
            assert!(
                self.is_live(*target as usize),
                "edge {slot} leads to a removed state"
            );
        }
        if let Some(incoming) = self.incoming.get() {
            incoming.check_against(&self.targets, n, true);
        }
    }

    /// The incoming edges, collected on first use.
    fn incoming(&self) -> &ReverseCsr {
        self.incoming
            .get_or_init(|| ReverseCsr::build(&self.targets, self.states.len()))
    }

    /// The slots of the edges that lead to `state`.
    fn slots_into(&self, state: usize) -> Vec<u32> {
        self.incoming()
            .to_state(state)
            .iter()
            .copied()
            .filter(|slot| self.targets[*slot as usize] as usize == state)
            .collect()
    }

    /// Writes the edge into `slot`, replacing the edge that was there. Both endpoints must exist.
    fn set_slot(&mut self, slot: usize, color: C, target: u32) -> EdgeId {
        let id = EdgeId(slot as u32);
        self.incoming.take();
        self.targets[slot] = target;
        self.colors[slot] = Some(color);
        id
    }

    /// The color of the edge with the given id, mutable.
    fn edge_color_slot_mut(&mut self, id: EdgeId) -> Option<&mut C> {
        let slot = id.0 as usize;
        if self.targets.get(slot).copied()? == NONE {
            return None;
        }
        self.colors[slot].as_mut()
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> ForAlphabet<A> for DenseTs<A, Q, C> {
    fn for_alphabet(alphabet: A) -> Self {
        Self::new(alphabet)
    }

    fn for_alphabet_size_hint(alphabet: A, size_hint: usize) -> Self {
        Self::with_capacity(alphabet, size_hint)
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> TransitionSystem for DenseTs<A, Q, C> {
    type Alphabet = A;
    type StateIndex = StateId;
    type StateColor = Q;
    type EdgeColor = C;
    type EdgesFromIter<'this>
        = DenseEdgesFrom<'this, A, Q, C>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        let q = state.into_usize();
        if !self.is_live(q) {
            return None;
        }
        Some(DenseEdgesFrom::new(self, state))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.states
            .get(state.into_usize())?
            .as_ref()
            .map(Cow::Borrowed)
    }

    fn state_bound(&self) -> Option<usize> {
        Some(self.states.len())
    }
}

/// Iterates over the edges that leave a state of a [`DenseTs`], in the order of the alphabet.
pub struct DenseEdgesFrom<'ts, A: IndexedAlphabet, Q, C> {
    alphabet: &'ts A,
    source: StateId,
    /// The slot of the next edge to look at.
    slot: usize,
    /// The index of the symbol of the next edge to look at.
    symbol_index: usize,
    targets: std::slice::Iter<'ts, u32>,
    colors: std::slice::Iter<'ts, Option<C>>,
    _ts: std::marker::PhantomData<fn() -> Q>,
}

impl<'ts, A: IndexedAlphabet, Q, C> DenseEdgesFrom<'ts, A, Q, C> {
    #[inline(always)]
    fn new(ts: &'ts DenseTs<A, Q, C>, state: StateId) -> Self {
        let k = ts.alphabet.size();
        let slots = state.into_usize() * k..(state.into_usize() + 1) * k;
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

impl<'ts, A: IndexedAlphabet, Q: Color, C: Color> Iterator for DenseEdgesFrom<'ts, A, Q, C> {
    type Item = EdgeOf<'ts, DenseTs<A, Q, C>>;

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
                        StateId::from(target),
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

impl<A: IndexedAlphabet, Q: Color, C: Color> States for DenseTs<A, Q, C> {
    type StatesIter<'this>
        = DenseStateIndices<'this, Q>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        DenseStateIndices(&self.states, 0)
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        self.is_live(index.into_usize())
    }

    /// Checks that no slot of a live state is empty, which takes O(n * k) time.
    fn is_complete(&self) -> bool {
        let k = self.alphabet.size();
        (0..self.states.len())
            .filter(|q| self.is_live(*q))
            .all(|q| self.targets[q * k..(q + 1) * k].iter().all(|t| *t != NONE))
    }
}

/// Iterates over the indices of the states of a [`DenseTs`], skipping removed ones.
pub struct DenseStateIndices<'ts, Q>(&'ts [Option<Q>], usize);

impl<Q> Iterator for DenseStateIndices<'_, Q> {
    type Item = StateId;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.0.get(self.1) {
            self.1 += 1;
            if state.is_some() {
                return Some(StateId::from_usize(self.1 - 1));
            }
        }
        None
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> Deterministic for DenseTs<A, Q, C> {
    // The slots of a removed state are empty and those of a state that never existed are out of
    // range, so neither needs a check of its own.
    #[inline]
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        let index = self.alphabet.try_symbol_to_index(symbol)?;
        let slot = self.slot(state.into_usize(), index);
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
        let slot = self.slot(
            state.into_usize(),
            self.alphabet.try_symbol_to_index(symbol)?,
        );
        self.targets
            .get(slot)
            .copied()
            .filter(|t| *t != NONE)
            .map(StateId::from)
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> Sproutable for DenseTs<A, Q, C> {
    type Storage = Dense;

    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        let k = self.alphabet.size();
        let id = u32::try_from(self.states.len())
            .ok()
            .filter(|id| *id != NONE)
            .expect("too many states for 32 bit ids");
        // every slot id must be a valid edge id
        u32::try_from((self.states.len() + 1) * k)
            .ok()
            .filter(|slots| *slots != NONE)
            .expect("too many edge slots for 32 bit ids");
        self.states.push(Some(color));
        self.targets.resize(self.targets.len() + k, NONE);
        self.colors.resize(self.colors.len() + k, None);
        self.incoming.take();
        StateId::from(id)
    }

    /// Adds the edge, which replaces the edge that leaves the same state on the same symbol.
    fn add_edge<E>(&mut self, t: E) -> EdgeId
    where
        E: IntoEdgeTuple<Self>,
    {
        let (q, a, c, p) = t.into_edge_tuple();
        assert!(
            self.is_live(q.into_usize()),
            "source state {q} does not exist"
        );
        assert!(
            self.is_live(p.into_usize()),
            "target state {p} does not exist"
        );

        let slot = self.slot(q.into_usize(), self.alphabet.expression_to_index(&a));
        self.set_slot(slot, c, p.into())
    }

    fn edge_color_mut(&mut self, id: EdgeId) -> Option<&mut EdgeColor<Self>> {
        self.edge_color_slot_mut(id)
    }

    /// Fills every empty slot with an edge to a new sink, in O(n * k) time. Nothing is added if the
    /// system is already complete.
    fn complete_with_colors(&mut self, sink_color: Self::StateColor, edge_color: Self::EdgeColor) {
        if self.is_complete() {
            return;
        }
        let k = self.alphabet.size();
        let sink = self.add_state(sink_color);
        // the sink is the last state and gets all its edges from the loop below
        for slot in 0..self.targets.len() {
            if self.targets[slot] == NONE && self.is_live(slot / k) {
                self.set_slot(slot, edge_color.clone(), sink.into());
            }
        }
    }

    fn state_color_mut(&mut self, state: StateIndex<Self>) -> Option<&mut StateColor<Self>> {
        self.states.get_mut(state.into_usize())?.as_mut()
    }

    fn map_edge_colors_in_place(&mut self, mut f: impl FnMut(&mut EdgeColor<Self>)) {
        for (target, color) in self.targets.iter().zip(self.colors.iter_mut()) {
            if *target != NONE {
                color.as_mut().map(&mut f);
            }
        }
    }

    fn map_state_colors_in_place(&mut self, mut f: impl FnMut(&mut StateColor<Self>)) {
        self.states.iter_mut().flatten().for_each(&mut f);
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> Shrinkable for DenseTs<A, Q, C> {
    fn remove_edge(&mut self, id: EdgeId) -> Option<EdgeTuple<Self>> {
        let slot = id.0 as usize;
        let target = self.targets.get(slot).copied().filter(|t| *t != NONE)?;
        let k = self.alphabet.size();
        self.targets[slot] = NONE;
        let color = self.colors[slot].take().expect("edge has a color");
        Some((
            StateId::from_usize(slot / k),
            self.alphabet.expression_from_index(slot % k),
            color,
            StateId::from(target),
        ))
    }

    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        let q = state.into_usize();
        if !self.is_live(q) {
            return None;
        }
        for slot in self.slots_of(q) {
            self.remove_edge(EdgeId(slot as u32));
        }
        // a loop was already removed with the outgoing edges
        for slot in self.slots_into(q) {
            self.remove_edge(EdgeId(slot));
        }
        self.states[q].take()
    }

    fn remove_edges_to(&mut self, target: StateIndex<Self>) -> Option<Vec<EdgeTuple<Self>>> {
        if !self.is_live(target.into_usize()) {
            return None;
        }
        let mut removed = Vec::new();
        for slot in self.slots_into(target.into_usize()) {
            removed.extend(self.remove_edge(EdgeId(slot)));
        }
        Some(removed)
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> PredecessorIterable for DenseTs<A, Q, C> {
    type EdgesToIter<'this>
        = DenseEdgesTo<'this, A, Q, C>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        let q = state.into_usize();
        self.is_live(q).then(|| DenseEdgesTo {
            ts: self,
            state,
            slots: self.incoming().to_state(q).iter(),
        })
    }
}

/// Iterates over the edges that enter a state of a [`DenseTs`], ordered by their slot.
pub struct DenseEdgesTo<'ts, A: IndexedAlphabet, Q, C> {
    ts: &'ts DenseTs<A, Q, C>,
    state: StateId,
    slots: std::slice::Iter<'ts, u32>,
}

impl<'ts, A: IndexedAlphabet, Q: Color, C: Color> Iterator for DenseEdgesTo<'ts, A, Q, C> {
    type Item = EdgeOf<'ts, DenseTs<A, Q, C>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (targets, state) = (&self.ts.targets, u32::from(self.state));
        let slot = *self.slots.find(|slot| targets[**slot as usize] == state)? as usize;
        let k = self.ts.alphabet.size();
        Some(
            self.ts
                .edge_in_slot(StateId::from_usize(slot / k), slot, slot % k)
                .expect("listed edge exists"),
        )
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.slots.len()))
    }

    #[inline]
    fn count(self) -> usize {
        let (targets, state) = (&self.ts.targets, u32::from(self.state));
        self.slots
            .filter(|slot| targets[**slot as usize] == state)
            .count()
    }
}

/// Iterator over the edges of a table-based system ([`DenseTs`], [`CsrTs`](crate::ts::CsrTs)) that
/// is consumed, in the order of the slots.
pub struct TableIntoEdges<A: IndexedAlphabet, C> {
    alphabet: A,
    /// The state and the symbol index of the next slot.
    next: (u32, usize),
    slots: std::iter::Zip<std::vec::IntoIter<u32>, std::vec::IntoIter<Option<C>>>,
}

impl<A: IndexedAlphabet, C> TableIntoEdges<A, C> {
    pub(super) fn new(alphabet: A, targets: Vec<u32>, colors: Vec<Option<C>>) -> Self {
        Self {
            alphabet,
            next: (0, 0),
            slots: targets.into_iter().zip(colors),
        }
    }
}

impl<A: IndexedAlphabet, C> Iterator for TableIntoEdges<A, C> {
    type Item = (StateId, A::Expression, C, StateId);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let k = self.alphabet.size();
        for (target, color) in self.slots.by_ref() {
            let (source, symbol_index) = self.next;
            self.next = if symbol_index + 1 == k {
                (source + 1, 0)
            } else {
                (source, symbol_index + 1)
            };
            if target != NONE {
                let expression = self.alphabet.expression_ref(symbol_index).clone();
                return Some((
                    StateId::from(source),
                    expression,
                    color.expect("edge has a color"),
                    StateId::from(target),
                ));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.slots.size_hint().1)
    }
}

/// Iterator over the states of a [`DenseTs`] that is consumed, skipping removed states.
pub struct DenseIntoStates<Q> {
    states: std::iter::Enumerate<std::vec::IntoIter<Option<Q>>>,
}

impl<Q> Iterator for DenseIntoStates<Q> {
    type Item = (StateId, Q);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.states
            .find_map(|(i, color)| color.map(|c| (StateId::from_usize(i), c)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.states.size_hint().1)
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> IntoTransitions for DenseTs<A, Q, C> {
    type Initial = ();
    type IntoStates = DenseIntoStates<Q>;
    type IntoEdges = TableIntoEdges<A, C>;

    fn into_transitions(self) -> Parts<A, Self::IntoStates, Self::IntoEdges, ()> {
        Parts {
            edges: TableIntoEdges::new(self.alphabet.clone(), self.targets, self.colors),
            states: DenseIntoStates {
                states: self.states.into_iter().enumerate(),
            },
            alphabet: self.alphabet,
            initial: (),
        }
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color, I: IdType, Init> FromTransitions<I, Init>
    for DenseTs<A, Q, C>
{
    /// Edges that leave the same state on the same symbol replace each other.
    fn from_transitions<S, E>(parts: Parts<A, S, E, Init>) -> Self
    where
        S: Iterator<Item = (I, Q)>,
        E: Iterator<Item = (I, A::Expression, C, I)>,
    {
        sprout_from_parts(parts)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::Storage;
    use crate::ts::q;

    fn triangle() -> DenseTs<CharAlphabet, Void, u32> {
        let mut ts = DenseTs::new(CharAlphabet::of_size(2));
        let q: Vec<_> = (0..3).map(|_| ts.add_state(Void)).collect();
        ts.add_edge((q[0], 'a', 1u32, q[1]));
        ts.add_edge((q[1], 'a', 2u32, q[2]));
        ts.add_edge((q[2], 'a', 3u32, q[0]));
        ts.add_edge((q[0], 'b', 4u32, q[0]));
        ts
    }

    #[test]
    fn lookup_and_edge_ids() {
        let ts = triangle();
        assert_eq!(ts.state_count(), 3);
        assert_eq!(ts.successor(q(0), 'a'), Some(q(1)));
        assert_eq!(ts.successor(q(2), 'a'), Some(q(0)));
        assert_eq!(ts.successor(q(1), 'b'), None);
        assert_eq!(ts.successor(q(0), 'z'), None);
        assert_eq!(ts.successor(q(7), 'a'), None);
        // slot = q * k + a
        assert_eq!(ts.edge(q(1), 'a').unwrap().id(), Some(EdgeId(2)));
        assert_eq!(*ts.edge(q(0), 'b').unwrap().color(), 4);
        assert_eq!(ts.edges_from(q(0)).unwrap().count(), 2);
        assert_eq!(ts.edges_from(q(7)).map(|_| ()), None);
    }

    #[test]
    fn insertion_overwrites_and_updates_predecessors() {
        let mut ts = triangle();
        let first = ts.edge(q(0), 'a').unwrap().id().unwrap();
        let second = ts.add_edge((q(0), 'a', 9u32, q(2)));
        assert_eq!(first, second);
        assert_eq!(ts.successor(q(0), 'a'), Some(q(2)));
        assert_eq!(*ts.edge(q(0), 'a').unwrap().color(), 9);
        assert_eq!(ts.predecessors(q(1)).unwrap().count(), 0);
        assert_eq!(ts.predecessors(q(2)).unwrap().count(), 2);
    }

    #[test]
    fn colors_are_mutable() {
        let mut ts = triangle();
        *ts.edge_color_mut(EdgeId(0)).unwrap() = 42;
        assert_eq!(*ts.edge(q(0), 'a').unwrap().color(), 42);
        assert!(ts.edge_color_mut(EdgeId(2)).is_some());
        assert!(ts.edge_color_mut(EdgeId(3)).is_none());
    }

    #[test]
    fn storage_converts_deterministic_linked() {
        let mut linked = crate::ts::LinkedTs::for_alphabet(CharAlphabet::of_size(2));
        let (q0, q1) = (linked.add_state(Void), linked.add_state(Void));
        linked.add_edge((q0, 'a', Void, q1));
        linked.add_edge((q1, 'b', Void, q0));
        let dense = <Dense as Storage<_>>::try_from_linked(linked.clone()).unwrap();
        assert_eq!(dense.successor(q(0), 'a'), Some(q(1)));
        assert_eq!(dense.successor(q(1), 'b'), Some(q(0)));
        assert_eq!(dense.successor(q(0), 'b'), None);

        linked.add_edge((q0, 'a', Void, q0));
        assert!(<Dense as Storage<_>>::try_from_linked(linked).is_err());
    }

    #[test]
    fn predecessors_follow_insertion_and_removal() {
        let mut ts = triangle();
        let into_zero = |ts: &DenseTs<CharAlphabet, Void, u32>| {
            let mut v: Vec<_> = ts
                .predecessors(q(0))
                .unwrap()
                .map(|e| (e.source(), *e.expression(), *e.color()))
                .collect();
            v.sort();
            v
        };
        assert_eq!(into_zero(&ts), vec![(q(0), 'b', 4), (q(2), 'a', 3)]);
        assert!(ts.predecessors(q(7)).is_none());

        assert_eq!(ts.remove_edge(EdgeId(4)), Some((q(2), 'a', 3, q(0))));
        assert_eq!(ts.remove_edge(EdgeId(4)), None);
        assert_eq!(into_zero(&ts), vec![(q(0), 'b', 4)]);
        assert_eq!(ts.successor(q(2), 'a'), None);
    }

    #[test]
    fn remove_state_removes_incident_edges() {
        let mut ts = triangle();
        assert_eq!(ts.remove_state(q(0)), Some(Void));
        assert_eq!(ts.remove_state(q(0)), None);
        assert!(!ts.contains_state(q(0)));
        assert_eq!(ts.states().collect::<Vec<_>>(), vec![q(1), q(2)]);
        assert_eq!(ts.successor(q(2), 'a'), None);
        assert_eq!(ts.predecessors(q(1)).unwrap().count(), 0);
        assert_eq!(ts.edges_from(q(0)).map(|_| ()), None);
        // the remaining edge keeps its id
        assert_eq!(ts.edge(q(1), 'a').unwrap().id(), Some(EdgeId(2)));
    }

    #[test]
    fn remove_edges_to_removes_loops_and_incoming() {
        let mut ts = triangle();
        assert_eq!(ts.remove_edges_to(q(0)).unwrap().len(), 2);
        assert_eq!(ts.remove_edges_to(q(7)), None);
        assert_eq!(ts.successor(q(0), 'b'), None);
        assert_eq!(ts.successor(q(0), 'a'), Some(q(1)));
    }

    #[test]
    fn completion() {
        let mut ts = triangle();
        assert!(!ts.is_complete());
        ts.remove_state(q(1));
        ts.complete_with_colors(Void, 7);
        assert!(ts.is_complete());
        // the sink is a new state, the removed state stays removed
        assert_eq!(ts.states().collect::<Vec<_>>(), vec![q(0), q(2), q(3)]);
        assert_eq!(ts.successor(q(0), 'a'), Some(q(3)));
        assert_eq!(ts.successor(q(2), 'b'), Some(q(3)));
        assert_eq!(ts.successor(q(3), 'a'), Some(q(3)));
        assert_eq!(*ts.edge(q(3), 'b').unwrap().color(), 7);
        assert_eq!(ts.successor(q(0), 'b'), Some(q(0)));

        ts.complete_with_colors(Void, 7);
        assert_eq!(ts.state_count(), 3);
    }
}
