use crate::prelude::*;

/// Represents an edge in a non-deterministic transition system, see [`NTS`]. It stores a color, an
/// expression, as well as a source and target state index. Moreover, it stores the indices of the
/// next and previous edge in the list of edges leaving the source state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct NTEdge<E, C> {
    pub(super) prev: Option<usize>,
    pub(super) source: usize,
    pub(super) target: usize,
    pub(super) color: C,
    pub(super) expression: E,
    pub(super) next: Option<usize>,
}

impl<'a, E, C: Clone> IsEdge<'a, E, usize, C> for &'a NTEdge<E, C> {
    fn target(&self) -> usize {
        self.target
    }

    fn color(&self) -> C {
        self.color.clone()
    }

    fn expression(&self) -> &'a E {
        &self.expression
    }

    fn source(&self) -> usize {
        self.source
    }
}

impl<E, C> NTEdge<E, C> {
    /// Creates a new edge with the given source, expression, color and target. The pointers
    /// to the next and previous edge are set to `None`.
    pub fn new(source: usize, expression: E, color: C, target: usize) -> Self {
        Self {
            prev: None,
            source,
            target,
            color,
            expression,
            next: None,
        }
    }

    /// Consumes `self` and applies the given function `f` to obtain a new color which is then
    /// combined with the remaining fields to form a recolored edge.
    pub fn recolor<D, F: Fn(C) -> D>(self, f: F) -> NTEdge<E, D> {
        NTEdge {
            prev: self.prev,
            source: self.source,
            target: self.target,
            color: f(self.color),
            expression: self.expression,
            next: self.next,
        }
    }
}
