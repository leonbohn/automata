use std::fmt::Debug;

use super::LinkedListTransitionSystemEdge;
use crate::Color;

/// Stores information characterizing a state in a non-deterministic transition system, see [`crate::NTS`].
/// It stores a color and a pointer to the index of the first edge leaving the state.
#[derive(Clone)]
pub enum LinkedListTransitionSystemState<Q> {
    Occupied(Q, Option<usize>, Option<usize>),
    Vacant,
}
use LinkedListTransitionSystemState::*;

impl<Q> LinkedListTransitionSystemState<Q> {
    pub fn map_occupied<QQ: Color, F>(self, f: F) -> LinkedListTransitionSystemState<QQ>
    where
        F: FnOnce(Q) -> QQ,
    {
        match self {
            Vacant => Vacant,
            Occupied(color, first_out_edge, first_in_edge) => {
                Occupied(f(color), first_out_edge, first_in_edge)
            }
        }
    }

    /// Create a new state with the given color.
    pub fn new(color: Q) -> Self {
        Self::Occupied(color, None, None)
    }

    pub fn color(&self) -> Option<&Q> {
        self.occupation().map(|c| c.0)
    }

    pub fn into_color(self) -> Option<Q> {
        match self {
            Occupied(c, _, _) => Some(c),
            Vacant => None,
        }
    }

    pub fn is_occupied(&self) -> bool {
        matches!(self, Occupied(_, _, _))
    }

    pub fn is_vacant(&self) -> bool {
        matches!(self, Vacant)
    }

    pub fn occupation(&self) -> Option<(&Q, Option<usize>, Option<usize>)> {
        match self {
            Occupied(color, first_out_edge, first_in_edge) => {
                Some((color, *first_out_edge, *first_in_edge))
            }
            Vacant => None,
        }
    }

    pub fn first_out_edge(&self) -> Option<usize> {
        self.occupation()?.1
    }

    pub fn set_first_out_edge(&mut self, first_edge: Option<usize>) {
        match self {
            Occupied(_, next_out, _) => *next_out = first_edge,
            Vacant => panic!("cannot set next edge on vacant state"),
        }
    }

    pub fn first_in_edge(&self) -> Option<usize> {
        self.occupation()?.2
    }

    pub fn set_first_in_edge(&mut self, first_edge: Option<usize>) {
        match self {
            Occupied(_, _, next_in) => *next_in = first_edge,
            Vacant => panic!("cannot set next edge on vacant state"),
        }
    }

    pub fn set_color(&mut self, color: Q) {
        match self {
            Occupied(c, _, _) => *c = color,
            Vacant => panic!("cannot set color on vacant state"),
        }
    }

    /// Applies the given recoloring function to produce a new [`LinkedListTransitionSystemState`] with color `C`.
    /// This method consumes `self`.
    pub fn recolor<C, F: Fn(Q) -> C>(self, f: F) -> LinkedListTransitionSystemState<C> {
        match self {
            Vacant => Vacant,
            Occupied(color, first_out_edge, first_in_edge) => {
                Occupied(f(color), first_out_edge, first_in_edge)
            }
        }
    }

    /// Marks the state as vacant and returns its color, if it had one.
    pub fn vacate(&mut self) -> Option<Q> {
        std::mem::replace(self, Self::Vacant).into_color()
    }

    pub(super) fn edges_from_iter<'a, E, C>(
        &self,
        array: &'a [LinkedListTransitionSystemEdge<E, C>],
    ) -> Option<NTSEdgesFromIter<'a, E, C>> {
        Some(NTSEdgesFromIter::new(array, self.occupation()?.1))
    }

    pub(super) fn zip_prepend<X>(self, x: X) -> LinkedListTransitionSystemState<(X, Q)> {
        match self {
            Vacant => Vacant,
            Occupied(color, first_out_edge, first_in_edge) => {
                Occupied((x, color), first_out_edge, first_in_edge)
            }
        }
    }
}
impl<Q, X> LinkedListTransitionSystemState<(X, Q)> {
    pub(super) fn unzip(self) -> LinkedListTransitionSystemState<Q> {
        match self {
            Vacant => Vacant,
            Occupied((_, color), first_out_edge, first_in_edge) => {
                Occupied(color, first_out_edge, first_in_edge)
            }
        }
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
        self.current = e.out_next;
        Some(e)
    }
}

impl<'a, E, C> NTSEdgesFromIter<'a, E, C> {
    /// Creates a new iterator over the edges leaving a state.
    pub fn new(edges: &'a [LinkedListTransitionSystemEdge<E, C>], current: Option<usize>) -> Self {
        Self { edges, current }
    }
}

/// Iterator over the edges in a [`crate::NTS`] that reach a certain state.
pub struct LinkedListTransitionSystemEdgesToIter<'a, E, C, const DET: bool> {
    edges: &'a [LinkedListTransitionSystemEdge<E, C>],
    current: Option<usize>,
}

impl<'a, E, C, const DET: bool> Iterator for LinkedListTransitionSystemEdgesToIter<'a, E, C, DET> {
    type Item = &'a LinkedListTransitionSystemEdge<E, C>;
    fn next(&mut self) -> Option<Self::Item> {
        let e = &self.edges[self.current?];
        self.current = e.in_next;
        Some(e)
    }
}

impl<'a, E, C, const DET: bool> LinkedListTransitionSystemEdgesToIter<'a, E, C, DET> {
    /// Creates a new iterator over the edges reaching a state.
    pub fn new(edges: &'a [LinkedListTransitionSystemEdge<E, C>], first_in: Option<usize>) -> Self {
        Self {
            edges,
            current: first_in,
        }
    }
}

impl<Q: Debug> Debug for LinkedListTransitionSystemState<Q> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Vacant => write!(f, "Vacant"),
            Occupied(_, first_out, first_in) => {
                write!(f, "Occupied[out:{first_out:?}|in:{first_in:?}]")
            }
        }
    }
}
