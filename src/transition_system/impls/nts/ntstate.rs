use crate::prelude::*;

use super::NTEdge;

/// Stores information characterizing a state in a non-deterministic transition system, see [`NTS`].
/// It stores a color and a pointer to the index of the first edge leaving the state.
#[derive(Clone)]
pub struct NTState<Q> {
    pub(super) color: Q,
    pub(super) first_edge: Option<usize>,
}

impl<Q> NTState<Q> {
    /// Create a new state with the given color.
    pub fn new(color: Q) -> Self {
        Self {
            color,
            first_edge: None,
        }
    }

    /// Applies the given recoloring function to produce a new [`NTState`] with color `C`.
    /// This method consumes `self`.
    pub fn recolor<C, F: Fn(Q) -> C>(self, f: F) -> NTState<C> {
        NTState {
            color: f(self.color),
            first_edge: self.first_edge,
        }
    }

    pub(super) fn edges_from_iter<'a, E, C>(
        &self,
        array: &'a [NTEdge<E, C>],
    ) -> NTSEdgesFromIter<'a, E, C> {
        NTSEdgesFromIter::new(array, self.first_edge)
    }
}

/// Iterator over the edges leaving a state in a non-deterministic transition system.
pub struct NTSEdgesFromIter<'a, E, C> {
    edges: &'a [NTEdge<E, C>],
    current: Option<usize>,
}

impl<'a, E, C> Iterator for NTSEdgesFromIter<'a, E, C> {
    type Item = &'a NTEdge<E, C>;
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
    pub fn new(edges: &'a [NTEdge<E, C>], current: Option<usize>) -> Self {
        Self { edges, current }
    }
}

/// Iterator over the edges in a [`NTS`] that reach a certain state.
pub struct NTSEdgesToIter<'a, E, C> {
    edges: std::slice::Iter<'a, NTEdge<E, C>>,
    target: usize,
}

impl<'a, E, C> Iterator for NTSEdgesToIter<'a, E, C> {
    type Item = &'a NTEdge<E, C>;
    fn next(&mut self) -> Option<Self::Item> {
        self.edges.find(|e| e.target == self.target)
    }
}

impl<'a, E, C> NTSEdgesToIter<'a, E, C> {
    /// Creates a new iterator over the edges reaching a state.
    pub fn new<A: Alphabet<Expression = E>, Q: Clone>(
        nts: &'a NTS<A, Q, C>,
        target: usize,
    ) -> Self {
        Self {
            edges: nts.edges.iter(),
            target,
        }
    }
}
