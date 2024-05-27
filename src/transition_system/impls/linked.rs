use std::{collections::BTreeSet, fmt::Debug, hash::Hash};

use crate::{math::Set, prelude::*, transition_system::Shrinkable, Void};
use itertools::Itertools;

mod linked_state;
pub use linked_state::{
    LinkedListTransitionSystemEdgesToIter, LinkedListTransitionSystemState, NTSEdgesFromIter,
};

mod linked_edge;
pub use linked_edge::LinkedListTransitionSystemEdge;
use tracing::trace;

/// Type alias for the constituent parts of an [`NTS`] with the same associated types as the
/// transition sytem `D`.
pub type IntoLinkedListNondeterministic<D> = (
    <D as TransitionSystem>::Alphabet,
    Vec<LinkedListTransitionSystemState<StateColor<D>>>,
    Vec<LinkedListTransitionSystemEdge<EdgeExpression<D>, EdgeColor<D>>>,
);

pub type LinkedListNondeterministic<A = CharAlphabet, Q = Void, C = Void> =
    LinkedListTransitionSystem<A, Q, C, false>;
pub type LinkedListDeterministic<A = CharAlphabet, Q = Void, C = Void> =
    LinkedListTransitionSystem<A, Q, C, true>;

/// Type alias to create a deterministic transition with the same alphabet, state and edge color
/// as the given [`Ts`](`crate::prelude::TransitionSystem`).
pub type CollectLinkedList<Ts, const DET: bool = true> = LinkedListTransitionSystem<
    <Ts as TransitionSystem>::Alphabet,
    <Ts as TransitionSystem>::StateColor,
    <Ts as TransitionSystem>::EdgeColor,
    DET,
>;

/// Represents a non-deterministic transition system. It stores an [`Alphabet`], a list of [`LinkedListTransitionSystemState`]s and a list of [`LinkedListTransitionSystemEdge`]s.
#[derive(Clone)]
pub struct LinkedListTransitionSystem<
    A: Alphabet = CharAlphabet,
    Q = Void,
    C = Void,
    const DET: bool = true,
> {
    alphabet: A,
    states: Vec<LinkedListTransitionSystemState<Q>>,
    edges: Vec<LinkedListTransitionSystemEdge<A::Expression, C>>,
}

impl<A: Alphabet, Q: Color, C: Color> Deterministic for LinkedListTransitionSystem<A, Q, C> {}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> Sproutable
    for LinkedListTransitionSystem<A, Q, C, DET>
{
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        let id = self.states.len();
        let state = LinkedListTransitionSystemState::new(color);
        self.states.push(state);
        id
    }
    fn set_state_color(&mut self, index: StateIndex<Self>, color: StateColor<Self>) {
        if index >= self.states.len() {
            panic!(
                "Index {index} is out of bounds, there are only {} states",
                self.states.len()
            );
        }
        self.states[index].color = color;
    }

    fn add_edge<E>(&mut self, t: E) -> Option<Self::EdgeRef<'_>>
    where
        E: IntoEdgeTuple<Self>,
    {
        let (q, a, c, p) = t.into_edge_tuple();

        if DET
            && self
                .edges_from(q)
                .unwrap()
                .any(|e| e.expression().overlaps(&a))
        {
            return None;
        }

        let mut edge = LinkedListTransitionSystemEdge::new(q, a, c, p);
        let edge_id = self.edges.len();

        if let Some(last_edge_id) = self.last_edge(q) {
            assert!(last_edge_id < self.edges.len());
            assert!(self.edges[last_edge_id].next.is_none());
            self.edges[last_edge_id].next = Some(edge_id);
            edge.prev = Some(last_edge_id);
        } else {
            assert!(self.states[q].first_edge.is_none());
            self.states[q].first_edge = Some(edge_id);
        }

        self.edges.push(edge);
        Some(self.edges.last().expect("We just added one element!"))
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> Shrinkable
    for LinkedListTransitionSystem<A, Q, C, DET>
{
    fn remove_edges_from_matching(
        &mut self,
        from: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let mut out = vec![];
        while let Some(pos) = self.edge_position(from, &matcher) {
            let edge = self.remove_edge(from, pos);
            out.push(IntoEdgeTuple::<Self>::into_edge_tuple(edge));
        }
        Some(out)
    }
    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        todo!()
    }

    fn remove_edges_between_matching(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }

    fn remove_edges_between(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }

    fn remove_edges_from(
        &mut self,
        source: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }

    fn remove_edges_to(
        &mut self,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }
}

impl<Q, C, const DET: bool> LinkedListTransitionSystem<CharAlphabet, Q, C, DET> {
    /// Returns a transition system builder for a non-deterministic transition system. This should be the main method for the
    /// construction of non-deterministic transition systems on the fly.
    ///
    /// # Example
    ///
    /// We want to create a DFA with two states 0 and 1 over the alphabet `['a', 'b']`. We want to add the following transitions:
    /// - From state 0 to state 0 on symbol 'a'
    /// - From state 0 to state 1 on symbol 'b'
    /// - From state 1 to state 1 on symbol 'a'
    /// - From state 1 to state 0 on symbol 'b'
    /// Further, state 0 should be initial and colored `true` and state 1 should be colored `false`. This can be done as follows
    /// ```
    /// use automata::prelude::*;
    ///
    /// let ts = TSBuilder::default()
    ///     .with_state_colors([true, false]) // colors given in the order of the states
    ///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 0)])
    ///     .into_dfa(0); // 0 is the initial state
    /// ```
    pub fn builder() -> TSBuilder<Q, C> {
        TSBuilder::default()
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> LinkedListTransitionSystem<A, Q, C, DET> {
    pub(crate) fn nts_remove_edge(
        &mut self,
        from: usize,
        on: &EdgeExpression<Self>,
    ) -> Option<(C, usize)> {
        let pos = self.edge_position(from, on)?;
        let (color, target) = (self.edges[pos].color.clone(), self.edges[pos].target);
        self.remove_edge(from, pos);
        Some((color, target))
    }

    pub(crate) fn nts_remove_transitions(
        &mut self,
        from: usize,
        on: SymbolOf<Self>,
    ) -> Set<(EdgeExpression<Self>, C, usize)>
    where
        C: Hash + Eq,
    {
        let mut set = Set::default();
        let mut current = self.first_edge(from);
        let mut to_remove = Vec::new();
        while let Some(idx) = current {
            let edge = &self.edges[idx];
            if edge.expression.symbols().contains(&on) {
                set.insert((edge.expression.clone(), edge.color.clone(), edge.target));
                to_remove.push((from, idx));
            }
            current = edge.next;
        }
        for (from, idx) in to_remove {
            self.remove_edge(from, idx);
        }
        set
    }

    /// This removes a state from the NTS and returns the color of the removed state.
    /// This method also removes any incoming edges to this state.
    pub(crate) fn nts_remove_state(&mut self, state: usize) -> Option<Q> {
        unimplemented!("This method is not yet implemented")
    }

    fn edge_position(&self, from: usize, matcher: impl Matcher<A::Expression>) -> Option<usize> {
        let mut idx = self.states.get(from)?.first_edge?;
        loop {
            // FIXME: Make this be a match
            if matcher.matches((&self.edges[idx]).expression()) {
                return Some(idx);
            }
            idx = self.edges[idx].next?;
        }
    }
    fn remove_edge(
        &mut self,
        from: usize,
        idx: usize,
    ) -> &LinkedListTransitionSystemEdge<A::Expression, C> {
        assert!(idx < self.edges.len());

        let pred = self.edges[idx].prev;
        let succ = self.edges[idx].next;

        if self.states[from].first_edge == Some(idx) {
            assert!(pred.is_none());
            self.states[from].first_edge = succ;
        } else {
            assert!(
                pred.is_some(),
                "This must exist, otherwise we would be first edge"
            );
            if succ.is_some() {
                self.edges[succ.unwrap()].prev = pred;
            }
            self.edges[pred.unwrap()].next = succ;
        }

        &self.edges[idx]
    }

    /// Builds a new non-deterministic transition system for the given alphabet with a specified capacity.
    pub fn with_capacity(alphabet: A, cap: usize) -> Self {
        Self {
            alphabet,
            states: Vec::with_capacity(cap),
            edges: Vec::with_capacity(cap),
        }
    }

    /// Turns `self` into a deterministic transition system. Panics if `self` is not deterministic.
    pub fn into_deterministic(self) -> LinkedListTransitionSystem<A, Q, C> {
        match self.try_into_deterministic() {
            Ok(ts) => ts,
            Err(ts) => {
                tracing::error!("Tried to convert non-deterministic transition system to deterministic one\n{:?}", ts);
                panic!("This transition system is not deterministic");
            }
        }
    }

    /// Turns `self` into a deterministic transition system. Panics if `self` is not deterministic.
    pub fn try_into_deterministic(self) -> Result<LinkedListTransitionSystem<A, Q, C, true>, Self> {
        if DET {
            if !self.is_deterministic() {
                tracing::error!("Tried to convert non-deterministic transition system to deterministic one\n{:?}", self);
                panic!("This transition system is not deterministic");
            }
            Ok(recast(self))
        } else if self.is_deterministic() {
            Ok(recast(self))
        } else {
            Err(self)
        }
    }

    pub fn into_nondeterministic(self) -> LinkedListNondeterministic<A, Q, C> {
        recast(self)
    }

    fn first_edge(&self, idx: usize) -> Option<usize> {
        self.states.get(idx)?.first_edge
    }

    fn last_edge(&self, idx: usize) -> Option<usize> {
        let mut current = self.states.get(idx)?.first_edge?;
        loop {
            assert!(
                current < self.edges.len(),
                "Edge with id {current} does not exist"
            );
            if let Some(x) = self.edges[current].next {
                current = x;
            } else {
                return Some(current);
            }
        }
    }

    /// Builds a new [`NTS`] from its constituent parts.
    pub fn from_parts(
        alphabet: A,
        states: Vec<LinkedListTransitionSystemState<Q>>,
        edges: Vec<LinkedListTransitionSystemEdge<A::Expression, C>>,
    ) -> Self {
        Self {
            alphabet,
            states,
            edges,
        }
    }

    /// Decomposes `self` into a tuple of its constituents.
    pub fn into_parts(self) -> IntoLinkedListNondeterministic<Self> {
        (self.alphabet, self.states, self.edges)
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> TransitionSystem
    for LinkedListTransitionSystem<A, Q, C, DET>
{
    type StateIndex = usize;

    type StateColor = Q;

    type EdgeColor = C;

    type EdgeRef<'this> = &'this LinkedListTransitionSystemEdge<A::Expression, C>
    where
        Self: 'this;

    type EdgesFromIter<'this> = NTSEdgesFromIter<'this, A::Expression, C>
    where
        Self: 'this;

    type StateIndices<'this> = std::ops::Range<usize>
    where
        Self: 'this;

    type Alphabet = A;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        0..self.states.len()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(NTSEdgesFromIter::new(&self.edges, self.first_edge(state)))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<&Self::StateColor> {
        if state >= self.states.len() {
            panic!(
                "index {state} is out of bounds, there are only {} states",
                self.states.len()
            );
        }
        assert!(state < self.states.len());
        self.states.get(state).map(|x| &x.color)
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> ForAlphabet<A>
    for LinkedListTransitionSystem<A, Q, C, DET>
{
    fn for_alphabet(alphabet: A) -> Self {
        Self {
            alphabet,
            states: vec![],
            edges: vec![],
        }
    }

    fn for_alphabet_size_hint(from: A, size_hint: usize) -> Self {
        Self {
            alphabet: from,
            states: Vec::with_capacity(size_hint),
            edges: vec![],
        }
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> PredecessorIterable
    for LinkedListTransitionSystem<A, Q, C, DET>
{
    type PreEdgeRef<'this> = &'this LinkedListTransitionSystemEdge<A::Expression, C>
    where
        Self: 'this;

    type EdgesToIter<'this> = LinkedListTransitionSystemEdgesToIter<'this, A::Expression, C, DET>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        assert!(state < self.states.len());

        Some(LinkedListTransitionSystemEdgesToIter::new(self, state))
    }
}

impl<A: Alphabet + PartialEq, Q: Hash + Debug + Eq, C: Hash + Debug + Eq, const DET: bool> PartialEq
    for LinkedListTransitionSystem<A, Q, C, DET>
{
    fn eq(&self, other: &Self) -> bool {
        if self.alphabet != other.alphabet || self.states.len() != other.states.len() {
            return false;
        }

        self.states.iter().zip(other.states.iter()).all(|(x, y)| {
            if x.color != y.color {
                return false;
            }
            let edges = x
                .edges_from_iter(&self.edges)
                .map(|e| (&e.expression, &e.color, e.target))
                .collect::<Set<_>>();

            y.edges_from_iter(&other.edges)
                .all(|e| edges.contains(&(&e.expression, &e.color, e.target)))
        })
    }
}

impl<A: Alphabet + PartialEq, Q: Hash + Debug + Eq, C: Hash + Debug + Eq, const DET: bool> Eq
    for LinkedListTransitionSystem<A, Q, C, DET>
{
}

impl<A: Alphabet + std::fmt::Debug, Q: Color, C: Color, const DET: bool> std::fmt::Debug
    for LinkedListTransitionSystem<A, Q, C, DET>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "alphabet: {:?}", self.alphabet)?;
        for (i, state) in self.states.iter().enumerate() {
            writeln!(f, "state {}: {:?}", i, state)?;
            for edge in self.edges_from(i).unwrap() {
                writeln!(f, "  {:?}", edge)?;
            }
        }
        Ok(())
    }
}

fn recast<A: Alphabet, Q: Color, C: Color, const DET: bool, const OUT_DET: bool>(
    ts: LinkedListTransitionSystem<A, Q, C, DET>,
) -> LinkedListTransitionSystem<A, Q, C, OUT_DET> {
    if !DET && OUT_DET && !ts.is_deterministic() {
        panic!("cannot convert non-deterministic transition system to deterministic");
    }
    let LinkedListTransitionSystem {
        alphabet,
        states,
        edges,
    } = ts;
    LinkedListTransitionSystem {
        alphabet,
        states,
        edges,
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::TSBuilder;

    #[test]
    fn nts_equality() {
        let first = TSBuilder::default()
            .with_state_colors([0, 1])
            .with_edges([
                (0, 'a', 100u32, 0),
                (0, 'b', 1000, 1),
                (1, 'a', 200, 0),
                (1, 'b', 2000, 1),
            ])
            .into_linked_list_deterministic();
        let second = TSBuilder::default()
            .with_state_colors([0, 1])
            .with_edges([
                (0, 'b', 1000, 1),
                (1, 'b', 2000, 1),
                (0, 'a', 100u32, 0),
                (1, 'a', 200, 0),
            ])
            .into_linked_list_deterministic();
        assert!(first == second, "equality should disregard order of edges");
    }
}
