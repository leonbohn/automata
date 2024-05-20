use crate::prelude::*;

use super::{LinkedListTransitionSystem, LinkedListTransitionSystemEdge};

/// Stores information characterizing a state in a non-deterministic transition system, see [`NTS`].
/// It stores a color and a pointer to the index of the first edge leaving the state.
#[derive(Clone, Debug)]
pub struct LinkedListTransitionSystemState<Q> {
    pub(super) color: Q,
    pub(super) first_edge: Option<usize>,
}

impl<Q> LinkedListTransitionSystemState<Q> {
    /// Create a new state with the given color.
    pub fn new(color: Q) -> Self {
        Self {
            color,
            first_edge: None,
        }
    }

    /// Applies the given recoloring function to produce a new [`LinkedListTransitionSystemState`] with color `C`.
    /// This method consumes `self`.
    pub fn recolor<C, F: Fn(Q) -> C>(self, f: F) -> LinkedListTransitionSystemState<C> {
        LinkedListTransitionSystemState {
            color: f(self.color),
            first_edge: self.first_edge,
        }
    }

    pub(super) fn edges_from_iter<'a, E, C>(
        &self,
        array: &'a [LinkedListTransitionSystemEdge<E, C>],
    ) -> NTSEdgesFromIter<'a, E, C> {
        NTSEdgesFromIter::new(array, self.first_edge)
    }
}

/// Iterator over the edges leaving a state in a non-deterministic transition system.
pub struct NTSEdgesFromIter<'a, E, C> {
    edges: &'a [LinkedListTransitionSystemEdge<E, C>],
    current: Option<usize>,
}

impl<'a, E, C> Iterator for NTSEdgesFromIter<'a, E, C> {
    type Item = &'a LinkedListTransitionSystemEdge<E, C>;
    fn next(&mut self) -> Option<Self::Item> {
        let idx = self.current?;
        assert!(idx < self.edges.len());
        let e = &self.edges[idx];
        self.current = e.next;
        Some(e)
    }
}

impl<'a, E, C> NTSEdgesFromIter<'a, E, C> {
    /// Creates a new iterator over the edges leaving a state.
    pub fn new(edges: &'a [LinkedListTransitionSystemEdge<E, C>], current: Option<usize>) -> Self {
        Self { edges, current }
    }
}

/// Iterator over the edges in a [`NTS`] that reach a certain state.
pub struct LinkedListTransitionSystemEdgesToIter<'a, E, C, const DET: bool> {
    edges: std::slice::Iter<'a, LinkedListTransitionSystemEdge<E, C>>,
    target: usize,
}

impl<'a, E, C, const DET: bool> Iterator for LinkedListTransitionSystemEdgesToIter<'a, E, C, DET> {
    type Item = &'a LinkedListTransitionSystemEdge<E, C>;
    fn next(&mut self) -> Option<Self::Item> {
        self.edges.find(|e| e.target == self.target)
    }
}

impl<'a, E, C, const DET: bool> LinkedListTransitionSystemEdgesToIter<'a, E, C, DET> {
    /// Creates a new iterator over the edges reaching a state.
    pub fn new<A: Alphabet<Expression = E>, Q: Clone>(
        nts: &'a LinkedListTransitionSystem<A, Q, C, DET>,
        target: usize,
    ) -> Self {
        Self {
            edges: nts.edges.iter(),
            target,
        }
    }
}
