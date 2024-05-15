use std::{collections::BTreeSet, hash::Hash};

use crate::{math::Set, prelude::*, Void};
use itertools::Itertools;

mod ntstate;
pub use ntstate::{NTSEdgesFromIter, NTSEdgesToIter, NTState};

mod ntedge;
pub use ntedge::NTEdge;
use tracing::trace;

/// Type alias for the constituent parts of an [`NTS`] with the same associated types as the
/// transition sytem `D`.
pub type NTSPartsFor<D> = (
    <D as TransitionSystem>::Alphabet,
    Vec<NTState<StateColor<D>>>,
    Vec<NTEdge<ExpressionOf<D>, EdgeColor<D>>>,
);

/// Represents a non-deterministic transition system. It stores an [`Alphabet`], a list of [`NTState`]s and a list of [`NTEdge`]s.
/// Each state
#[derive(Clone)]
pub struct NTS<A: Alphabet = CharAlphabet, Q = Void, C = Void> {
    alphabet: A,
    states: Vec<NTState<Q>>,
    edges: Vec<NTEdge<A::Expression, C>>,
}

impl<A: Alphabet, Q: Clone, C: Clone> ForAlphabet for NTS<A, Q, C> {
    fn for_alphabet(alphabet: Self::Alphabet) -> Self {
        Self {
            alphabet,
            states: vec![],
            edges: vec![],
        }
    }
}

impl<A: Alphabet, Q: Clone, C: Clone> Sproutable for NTS<A, Q, C> {
    fn add_state<X: Into<StateColor<Self>>>(&mut self, color: X) -> Self::StateIndex {
        let id = self.states.len();
        let state = NTState::new(color.into());
        self.states.push(state);
        id
    }

    type ExtendStateIndexIter = std::ops::Range<usize>;

    fn extend_states<I: IntoIterator<Item = StateColor<Self>>>(
        &mut self,
        iter: I,
    ) -> Self::ExtendStateIndexIter {
        let i = self.states.len();
        for state in iter.into_iter() {
            self.add_state(state);
        }
        i..self.states.len()
    }

    fn set_state_color<Idx: Indexes<Self>, X: Into<StateColor<Self>>>(
        &mut self,
        index: Idx,
        color: X,
    ) {
        let Some(index) = index.to_index(self) else {
            tracing::error!("cannot set color of state that does not exist");
            return;
        };
        if index >= self.states.len() {
            panic!(
                "Index {index} is out of bounds, there are only {} states",
                self.states.len()
            );
        }
        self.states[index].color = color.into();
    }

    fn add_edge<X, Y, CI>(
        &mut self,
        from: X,
        on: <Self::Alphabet as Alphabet>::Expression,
        to: Y,
        color: CI,
    ) -> Option<(Self::StateIndex, Self::EdgeColor)>
    where
        X: Indexes<Self>,
        Y: Indexes<Self>,
        CI: Into<EdgeColor<Self>>,
    {
        let source = from.to_index(self)?;
        let target = to.to_index(self)?;

        let mut edge = NTEdge::new(source, on, color.into(), target);
        let edge_id = self.edges.len();

        if let Some(last_edge_id) = self.last_edge(source) {
            assert!(last_edge_id < self.edges.len());
            assert!(self.edges[last_edge_id].next.is_none());
            self.edges[last_edge_id].next = Some(edge_id);
            edge.prev = Some(last_edge_id);
        } else {
            assert!(self.states[source].first_edge.is_none());
            self.states[source].first_edge = Some(edge_id);
        }
        self.edges.push(edge);
        None
    }

    fn remove_edges<X: Indexes<Self>>(
        &mut self,
        from: X,
        on: <Self::Alphabet as Alphabet>::Expression,
    ) -> bool {
        let Some(from) = from.to_index(self) else {
            return false;
        };
        let mut b = false;
        while let Some(pos) = self.edge_position(from, &on) {
            self.remove_edge(from, pos);
            b = true;
        }
        b
    }
}

impl<Q, C> NTS<CharAlphabet, Q, C> {
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

impl<A: Alphabet, Q: Clone, C: Clone> NTS<A, Q, C> {
    pub(crate) fn nts_remove_edge(
        &mut self,
        from: usize,
        on: &ExpressionOf<Self>,
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
    ) -> Set<(ExpressionOf<Self>, C, usize)>
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

    fn edge_position(&self, from: usize, on: &A::Expression) -> Option<usize> {
        let mut idx = self.states.get(from)?.first_edge?;
        loop {
            // FIXME: Make this be a match
            if (&self.edges[idx]).expression() == on {
                return Some(idx);
            }
            idx = self.edges[idx].next?;
        }
    }
    fn remove_edge(&mut self, from: usize, idx: usize) {
        assert!(idx < self.edges.len());

        let pred = self.edges[idx].prev;
        let succ = self.edges[idx].next;

        if self.states[from].first_edge == Some(idx) {
            assert!(pred.is_none());
            self.states[from].first_edge = succ;
            return;
        }

        assert!(
            pred.is_some(),
            "This must exist, otherwise we would be first edge"
        );
        if succ.is_some() {
            self.edges[succ.unwrap()].prev = pred;
        }
        self.edges[pred.unwrap()].next = succ;
    }
    /// Builds a new non-deterministic transition system for the given alphabet with a specified capacity.
    pub fn with_capacity(alphabet: A, cap: usize) -> Self {
        Self {
            alphabet,
            states: Vec::with_capacity(cap),
            edges: Vec::with_capacity(cap),
        }
    }
    /// Returns true if the transition system is deterministic, i.e. if there are no two edges leaving
    /// the same state with the same symbol.
    pub fn is_deterministic(&self) -> bool {
        for state in self.state_indices() {
            for (l, r) in self
                .edges_from(state)
                .unwrap()
                .zip(self.edges_from(state).unwrap().skip(1))
            {
                if self.alphabet().overlapping(l.expression(), r.expression()) {
                    trace!(
                        "found overlapping edges from {}: on {} to {} and on {} to {}",
                        l.source(),
                        l.expression().show(),
                        l.target(),
                        r.expression().show(),
                        r.target(),
                    );
                    return false;
                }
            }
        }
        true
    }

    /// Turns `self` into a deterministic transition system. Panics if `self` is not deterministic.
    pub fn into_deterministic(self) -> DTS<A, Q, C> {
        debug_assert!(self.is_deterministic());
        DTS(self)
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
        states: Vec<NTState<Q>>,
        edges: Vec<NTEdge<A::Expression, C>>,
    ) -> Self {
        Self {
            alphabet,
            states,
            edges,
        }
    }

    /// Decomposes `self` into a tuple of its constituents.
    pub fn into_parts(self) -> NTSPartsFor<Self> {
        (self.alphabet, self.states, self.edges)
    }
}

impl<A: Alphabet, Q: Clone, C: Clone> TransitionSystem for NTS<A, Q, C> {
    type StateIndex = usize;

    type StateColor = Q;

    type EdgeColor = C;

    type EdgeRef<'this> = &'this NTEdge<A::Expression, C>
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

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        Some(NTSEdgesFromIter::new(
            &self.edges,
            self.first_edge(state.to_index(self)?),
        ))
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        let state = state.to_index(self)?;
        if state >= self.states.len() {
            panic!(
                "index {state} is out of bounds, there are only {} states",
                self.states.len()
            );
        }
        assert!(state < self.states.len());
        self.states.get(state).map(|x| x.color.clone())
    }
}

impl<A: Alphabet, Q: Clone, C: Clone> PredecessorIterable for NTS<A, Q, C> {
    type PreEdgeRef<'this> = &'this NTEdge<A::Expression, C>
    where
        Self: 'this;

    type EdgesToIter<'this> = NTSEdgesToIter<'this, A::Expression, C>
    where
        Self: 'this;

    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        let state = state.to_index(self)?;
        assert!(state < self.states.len());

        Some(NTSEdgesToIter::new(self, state))
    }
}

impl<A: Alphabet + PartialEq, Q: Hash + Eq, C: Hash + Eq> PartialEq for NTS<A, Q, C> {
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

impl<A: Alphabet + PartialEq, Q: Hash + Eq, C: Hash + Eq> Eq for NTS<A, Q, C> {}

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
            .into_dts();
        let second = TSBuilder::default()
            .with_state_colors([0, 1])
            .with_edges([
                (0, 'b', 1000, 1),
                (1, 'b', 2000, 1),
                (0, 'a', 100u32, 0),
                (1, 'a', 200, 0),
            ])
            .into_dts();
        assert!(first == second, "equality should disregard order of edges");
    }
}
