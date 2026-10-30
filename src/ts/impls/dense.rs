use std::borrow::Cow;

use crate::{
    Color, TransitionSystem, Void,
    alphabet::{CharAlphabet, IndexedAlphabet},
    ts::{
        DefaultIdType, Dense, Deterministic, EdgeColor, EdgeId, EdgeOf, EdgeRef, EdgeTuple,
        ForAlphabet, IntoEdgeTuple, Shrinkable, Sproutable, StateColor, StateIndex, States,
        SymbolOf, predecessors::PredecessorIterable,
    },
};

/// The sentinel that stands for "no edge" in the target slots of [`DenseTs`].
pub(super) const NONE: DefaultIdType = DefaultIdType::MAX;

/// A deterministic transition system over an [`IndexedAlphabet`] that stores the transitions in a
/// table with one slot per state and symbol.
///
/// # Layout
/// For `n` states and an alphabet of size `k`, the edge leaving state `q` on the symbol with
/// index `a` lives in slot `q * k + a`, which is also its [`EdgeId`]. Looking up an edge is thus one
/// index computation and a load. The targets and colors of the slots are kept in two separate
/// vectors, a target of [`NONE`] marks an absent edge.
///
/// No expression is stored per edge, it is lent out by the alphabet via
/// [`IndexedAlphabet::expression_ref`].
///
/// Every state keeps a list of its incoming [`EdgeId`]s so that predecessors are available.
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
    targets: Vec<DefaultIdType>,
    colors: Vec<Option<C>>,
    predecessors: Vec<Vec<EdgeId>>,
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
            predecessors: Vec::with_capacity(cap),
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

    /// The edge in slot `slot` leaving `source`, if there is one.
    #[inline(always)]
    fn edge_in_slot(&self, source: DefaultIdType, slot: usize) -> Option<EdgeOf<'_, Self>> {
        let target = self.targets[slot];
        if target == NONE {
            return None;
        }
        let k = self.alphabet.size();
        Some(
            EdgeRef::borrowed(
                source,
                self.alphabet.expression_ref(slot % k),
                self.colors[slot].as_ref().expect("edge has a color"),
                target,
            )
            .with_id(EdgeId(slot as u32)),
        )
    }

    /// Writes the edge into `slot`, replacing the edge that was there, and keeps the predecessors
    /// up to date. Both endpoints must exist.
    fn set_slot(&mut self, slot: usize, color: C, target: DefaultIdType) -> EdgeId {
        let id = EdgeId(slot as u32);
        let old = std::mem::replace(&mut self.targets[slot], target);
        if old != NONE {
            let incoming = &mut self.predecessors[old as usize];
            let position = incoming
                .iter()
                .position(|e| *e == id)
                .expect("edge is listed at its target");
            incoming.swap_remove(position);
        }
        self.colors[slot] = Some(color);
        self.predecessors[target as usize].push(id);
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
    type StateIndex = DefaultIdType;
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
        let q = state as usize;
        if !self.is_live(q) {
            return None;
        }
        Some(DenseEdgesFrom {
            ts: self,
            source: state,
            slots: self.slots_of(q),
        })
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.states.get(state as usize)?.as_ref().map(Cow::Borrowed)
    }

    fn state_bound(&self) -> Option<usize> {
        Some(self.states.len())
    }
}

/// Iterates over the edges that leave a state of a [`DenseTs`], in the order of the alphabet.
pub struct DenseEdgesFrom<'ts, A: IndexedAlphabet, Q, C> {
    ts: &'ts DenseTs<A, Q, C>,
    source: DefaultIdType,
    slots: std::ops::Range<usize>,
}

impl<'ts, A: IndexedAlphabet, Q: Color, C: Color> Iterator for DenseEdgesFrom<'ts, A, Q, C> {
    type Item = EdgeOf<'ts, DenseTs<A, Q, C>>;

    fn next(&mut self) -> Option<Self::Item> {
        for slot in self.slots.by_ref() {
            if let Some(edge) = self.ts.edge_in_slot(self.source, slot) {
                return Some(edge);
            }
        }
        None
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
        self.is_live(index as usize)
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
    type Item = DefaultIdType;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.0.get(self.1) {
            self.1 += 1;
            if state.is_some() {
                return Some((self.1 - 1) as DefaultIdType);
            }
        }
        None
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> Deterministic for DenseTs<A, Q, C> {
    #[inline]
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        let q = state as usize;
        if !self.is_live(q) || !self.alphabet.contains(symbol) {
            return None;
        }
        self.edge_in_slot(state, self.slot(q, self.alphabet.symbol_to_index(symbol)))
    }

    #[inline]
    fn successor(
        &self,
        state: StateIndex<Self>,
        symbol: SymbolOf<Self>,
    ) -> Option<StateIndex<Self>> {
        let q = state as usize;
        if !self.is_live(q) || !self.alphabet.contains(symbol) {
            return None;
        }
        let target = self.targets[self.slot(q, self.alphabet.symbol_to_index(symbol))];
        (target != NONE).then_some(target)
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> Sproutable for DenseTs<A, Q, C> {
    type Storage = Dense;

    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        let k = self.alphabet.size();
        let id = DefaultIdType::try_from(self.states.len())
            .ok()
            .filter(|id| *id != NONE)
            .expect("too many states for 32 bit ids");
        // every slot id must be a valid edge id
        DefaultIdType::try_from((self.states.len() + 1) * k)
            .ok()
            .filter(|slots| *slots != NONE)
            .expect("too many edge slots for 32 bit ids");
        self.states.push(Some(color));
        self.targets.resize(self.targets.len() + k, NONE);
        self.colors.resize(self.colors.len() + k, None);
        self.predecessors.push(Vec::new());
        id
    }

    /// Adds the edge, which replaces the edge that leaves the same state on the same symbol.
    fn add_edge<E>(&mut self, t: E) -> EdgeId
    where
        E: IntoEdgeTuple<Self>,
    {
        let (q, a, c, p) = t.into_edge_tuple();
        assert!(self.is_live(q as usize), "source state {q} does not exist");
        assert!(self.is_live(p as usize), "target state {p} does not exist");

        let slot = self.slot(q as usize, self.alphabet.expression_to_index(&a));
        self.set_slot(slot, c, p)
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
                self.set_slot(slot, edge_color.clone(), sink);
            }
        }
    }

    fn state_color_mut(&mut self, state: StateIndex<Self>) -> Option<&mut StateColor<Self>> {
        self.states.get_mut(state as usize)?.as_mut()
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> Shrinkable for DenseTs<A, Q, C> {
    fn remove_edge(&mut self, id: EdgeId) -> Option<EdgeTuple<Self>> {
        let slot = id.0 as usize;
        let target = self.targets.get(slot).copied().filter(|t| *t != NONE)?;
        let k = self.alphabet.size();
        let incoming = &mut self.predecessors[target as usize];
        let position = incoming
            .iter()
            .position(|e| *e == id)
            .expect("edge is listed at its target");
        incoming.swap_remove(position);
        self.targets[slot] = NONE;
        let color = self.colors[slot].take().expect("edge has a color");
        Some((
            (slot / k) as DefaultIdType,
            self.alphabet.expression_from_index(slot % k),
            color,
            target,
        ))
    }

    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        let q = state as usize;
        if !self.is_live(q) {
            return None;
        }
        for slot in self.slots_of(q) {
            self.remove_edge(EdgeId(slot as u32));
        }
        // a loop was already removed with the outgoing edges
        while let Some(id) = self.predecessors[q].last().copied() {
            self.remove_edge(id);
        }
        self.states[q].take()
    }

    fn remove_edges_to(&mut self, target: StateIndex<Self>) -> Option<Vec<EdgeTuple<Self>>> {
        if !self.is_live(target as usize) {
            return None;
        }
        let ids = self.predecessors[target as usize].clone();
        Some(
            ids.into_iter()
                .filter_map(|id| self.remove_edge(id))
                .collect(),
        )
    }
}

impl<A: IndexedAlphabet, Q: Color, C: Color> PredecessorIterable for DenseTs<A, Q, C> {
    type EdgesToIter<'this>
        = DenseEdgesTo<'this, A, Q, C>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        let q = state as usize;
        self.is_live(q).then(|| DenseEdgesTo {
            ts: self,
            ids: self.predecessors[q].iter(),
        })
    }
}

/// Iterates over the edges that enter a state of a [`DenseTs`], in no particular order.
pub struct DenseEdgesTo<'ts, A: IndexedAlphabet, Q, C> {
    ts: &'ts DenseTs<A, Q, C>,
    ids: std::slice::Iter<'ts, EdgeId>,
}

impl<'ts, A: IndexedAlphabet, Q: Color, C: Color> Iterator for DenseEdgesTo<'ts, A, Q, C> {
    type Item = EdgeOf<'ts, DenseTs<A, Q, C>>;

    fn next(&mut self) -> Option<Self::Item> {
        let slot = self.ids.next()?.0 as usize;
        let source = (slot / self.ts.alphabet.size()) as DefaultIdType;
        Some(
            self.ts
                .edge_in_slot(source, slot)
                .expect("listed edge exists"),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::Storage;

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
        assert_eq!(ts.successor(0, 'a'), Some(1));
        assert_eq!(ts.successor(2, 'a'), Some(0));
        assert_eq!(ts.successor(1, 'b'), None);
        assert_eq!(ts.successor(0, 'z'), None);
        assert_eq!(ts.successor(7, 'a'), None);
        // slot = q * k + a
        assert_eq!(ts.edge(1, 'a').unwrap().id(), Some(EdgeId(2)));
        assert_eq!(*ts.edge(0, 'b').unwrap().color(), 4);
        assert_eq!(ts.edges_from(0).unwrap().count(), 2);
        assert_eq!(ts.edges_from(7).map(|_| ()), None);
    }

    #[test]
    fn insertion_overwrites_and_updates_predecessors() {
        let mut ts = triangle();
        let first = ts.edge(0, 'a').unwrap().id().unwrap();
        let second = ts.add_edge((0, 'a', 9u32, 2));
        assert_eq!(first, second);
        assert_eq!(ts.successor(0, 'a'), Some(2));
        assert_eq!(*ts.edge(0, 'a').unwrap().color(), 9);
        assert!(ts.predecessors[1].is_empty());
        assert_eq!(ts.predecessors[2].len(), 2);
    }

    #[test]
    fn colors_are_mutable() {
        let mut ts = triangle();
        *ts.edge_color_mut(EdgeId(0)).unwrap() = 42;
        assert_eq!(*ts.edge(0, 'a').unwrap().color(), 42);
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
        assert_eq!(dense.successor(0, 'a'), Some(1));
        assert_eq!(dense.successor(1, 'b'), Some(0));
        assert_eq!(dense.successor(0, 'b'), None);

        linked.add_edge((q0, 'a', Void, q0));
        assert!(<Dense as Storage<_>>::try_from_linked(linked).is_err());
    }

    #[test]
    fn predecessors_follow_insertion_and_removal() {
        let mut ts = triangle();
        let into_zero = |ts: &DenseTs<CharAlphabet, Void, u32>| {
            let mut v: Vec<_> = ts
                .predecessors(0)
                .unwrap()
                .map(|e| (e.source(), *e.expression(), *e.color()))
                .collect();
            v.sort();
            v
        };
        assert_eq!(into_zero(&ts), vec![(0, 'b', 4), (2, 'a', 3)]);
        assert!(ts.predecessors(7).is_none());

        assert_eq!(ts.remove_edge(EdgeId(4)), Some((2, 'a', 3, 0)));
        assert_eq!(ts.remove_edge(EdgeId(4)), None);
        assert_eq!(into_zero(&ts), vec![(0, 'b', 4)]);
        assert_eq!(ts.successor(2, 'a'), None);
    }

    #[test]
    fn remove_state_removes_incident_edges() {
        let mut ts = triangle();
        assert_eq!(ts.remove_state(0), Some(Void));
        assert_eq!(ts.remove_state(0), None);
        assert!(!ts.contains_state(0));
        assert_eq!(ts.states().collect::<Vec<_>>(), vec![1, 2]);
        assert_eq!(ts.successor(2, 'a'), None);
        assert_eq!(ts.predecessors(1).unwrap().count(), 0);
        assert_eq!(ts.edges_from(0).map(|_| ()), None);
        // the remaining edge keeps its id
        assert_eq!(ts.edge(1, 'a').unwrap().id(), Some(EdgeId(2)));
    }

    #[test]
    fn remove_edges_to_removes_loops_and_incoming() {
        let mut ts = triangle();
        assert_eq!(ts.remove_edges_to(0).unwrap().len(), 2);
        assert_eq!(ts.remove_edges_to(7), None);
        assert_eq!(ts.successor(0, 'b'), None);
        assert_eq!(ts.successor(0, 'a'), Some(1));
    }

    #[test]
    fn completion() {
        let mut ts = triangle();
        assert!(!ts.is_complete());
        ts.remove_state(1);
        ts.complete_with_colors(Void, 7);
        assert!(ts.is_complete());
        // the sink is a new state, the removed state stays removed
        assert_eq!(ts.states().collect::<Vec<_>>(), vec![0, 2, 3]);
        assert_eq!(ts.successor(0, 'a'), Some(3));
        assert_eq!(ts.successor(2, 'b'), Some(3));
        assert_eq!(ts.successor(3, 'a'), Some(3));
        assert_eq!(*ts.edge(3, 'b').unwrap().color(), 7);
        assert_eq!(ts.successor(0, 'b'), Some(0));

        ts.complete_with_colors(Void, 7);
        assert_eq!(ts.state_count(), 3);
    }
}
