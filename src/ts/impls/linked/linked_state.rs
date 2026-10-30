use std::fmt::Debug;

use super::linked_edge::{LinkedEdge, NONE};
use crate::ts::{DefaultIdType, EdgeRef};

/// A state of the linked storage: its color and the heads of its out- and in-list. A removed state
/// is [`LinkedState::Vacant`] and keeps its slot, so that the ids of all other states stay valid.
#[derive(Clone)]
pub(super) enum LinkedState<Q> {
    Occupied(Q, u32, u32),
    Vacant,
}
use LinkedState::*;

impl<Q> LinkedState<Q> {
    pub(super) fn new(color: Q) -> Self {
        Occupied(color, NONE, NONE)
    }

    pub(super) fn map_occupied<QQ>(self, f: impl FnOnce(Q) -> QQ) -> LinkedState<QQ> {
        match self {
            Vacant => Vacant,
            Occupied(color, out, inn) => Occupied(f(color), out, inn),
        }
    }

    pub(super) fn color(&self) -> Option<&Q> {
        match self {
            Occupied(c, _, _) => Some(c),
            Vacant => None,
        }
    }

    pub(super) fn color_mut(&mut self) -> Option<&mut Q> {
        match self {
            Occupied(c, _, _) => Some(c),
            Vacant => None,
        }
    }

    #[inline]
    pub(super) fn is_occupied(&self) -> bool {
        matches!(self, Occupied(..))
    }

    pub(super) fn is_vacant(&self) -> bool {
        matches!(self, Vacant)
    }

    /// The head of the out-list, [`NONE`] if it is empty or the state is vacant.
    #[inline]
    pub(super) fn first_out_edge(&self) -> u32 {
        match self {
            Occupied(_, out, _) => *out,
            Vacant => NONE,
        }
    }

    /// The head of the in-list, [`NONE`] if it is empty or the state is vacant.
    #[inline]
    pub(super) fn first_in_edge(&self) -> u32 {
        match self {
            Occupied(_, _, inn) => *inn,
            Vacant => NONE,
        }
    }

    #[inline]
    pub(super) fn set_first_out_edge(&mut self, edge: u32) {
        match self {
            Occupied(_, out, _) => *out = edge,
            Vacant => unreachable!("a vacant state has no edges"),
        }
    }

    #[inline]
    pub(super) fn set_first_in_edge(&mut self, edge: u32) {
        match self {
            Occupied(_, _, inn) => *inn = edge,
            Vacant => unreachable!("a vacant state has no edges"),
        }
    }

    /// Marks the state as vacant and returns its color, if it had one.
    pub(super) fn vacate(&mut self) -> Option<Q> {
        match std::mem::replace(self, Vacant) {
            Occupied(c, _, _) => Some(c),
            Vacant => None,
        }
    }
}

/// Iterator over the edges leaving a state of a [`LinkedTs`](super::LinkedTs).
pub struct LinkedEdgesFrom<'a, E, C> {
    edges: &'a [LinkedEdge<E, C>],
    current: u32,
}

impl<'a, E, C> LinkedEdgesFrom<'a, E, C> {
    pub(super) fn new(edges: &'a [LinkedEdge<E, C>], first: u32) -> Self {
        Self {
            edges,
            current: first,
        }
    }
}

impl<'a, E, C: Clone> Iterator for LinkedEdgesFrom<'a, E, C> {
    type Item = EdgeRef<'a, DefaultIdType, E, C>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.current == NONE {
            return None;
        }
        let id = self.current;
        let e = &self.edges[id as usize];
        self.current = e.out_next;
        Some(e.as_edge_ref())
    }
}

/// Iterator over the edges of a [`LinkedTs`](super::LinkedTs) that reach a state.
pub struct LinkedEdgesTo<'a, E, C> {
    edges: &'a [LinkedEdge<E, C>],
    current: u32,
}

impl<'a, E, C> LinkedEdgesTo<'a, E, C> {
    pub(super) fn new(edges: &'a [LinkedEdge<E, C>], first: u32) -> Self {
        Self {
            edges,
            current: first,
        }
    }
}

impl<'a, E, C: Clone> Iterator for LinkedEdgesTo<'a, E, C> {
    type Item = EdgeRef<'a, DefaultIdType, E, C>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.current == NONE {
            return None;
        }
        let id = self.current;
        let e = &self.edges[id as usize];
        self.current = e.in_next;
        Some(e.as_edge_ref())
    }
}

impl<Q: Debug> Debug for LinkedState<Q> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Vacant => write!(f, "Vacant"),
            Occupied(_, out, inn) => {
                let show = |x: u32| if x == NONE { -1 } else { x as i64 };
                write!(f, "Occupied[out:{}|in:{}]", show(*out), show(*inn))
            }
        }
    }
}
