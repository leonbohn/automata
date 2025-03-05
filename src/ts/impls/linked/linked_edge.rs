use super::LinkedListTransitionSystem;
use crate::core::{Color, Void, alphabet::Alphabet};
use crate::ts::{DefaultIdType, IntoEdgeTuple, IsEdge, ScalarIndexType};
use std::fmt::Debug;

/// Represents an edge in a non-deterministic transition system, see [`crate::NTS`]. It stores a color, an
/// expression, as well as a source and target state index. Moreover, it stores the indices of the
/// next and previous edge in the list of edges leaving the source state.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct LinkedListTransitionSystemEdge<E, C> {
    pub(super) out_prev: Option<usize>,
    pub(super) in_prev: Option<usize>,
    pub(super) source: usize,
    pub(super) target: usize,
    pub(super) color: C,
    pub(super) expression: E,
    pub(super) out_next: Option<usize>,
    pub(super) in_next: Option<usize>,
}

impl<E, C> LinkedListTransitionSystemEdge<E, C> {
    pub fn map<CC: Color, F>(self, f: F) -> LinkedListTransitionSystemEdge<E, CC>
    where
        F: FnOnce(usize, E, C, usize) -> (E, CC),
    {
        let (expression, color) = f(self.source, self.expression, self.color, self.target);
        LinkedListTransitionSystemEdge {
            out_prev: self.out_prev,
            source: self.source,
            target: self.target,
            color,
            expression,
            out_next: self.out_next,
            in_prev: self.in_prev,
            in_next: self.in_next,
        }
    }

    pub fn borrowed_tuple<Idx: ScalarIndexType>(&self) -> (Idx, &E, &C, Idx) {
        (
            Idx::from_usize(self.source),
            &self.expression,
            &self.color,
            Idx::from_usize(self.target),
        )
    }

    pub fn into_tuple<Idx: ScalarIndexType>(self) -> (Idx, E, C, Idx) {
        (
            Idx::from_usize(self.source),
            self.expression,
            self.color,
            Idx::from_usize(self.target),
        )
    }

    /// Creates a new edge with the given source, expression, color and target. The pointers
    /// to the next and previous edge are set to `None`.
    pub fn new(source: DefaultIdType, expression: E, color: C, target: DefaultIdType) -> Self {
        Self {
            out_prev: None,
            in_next: None,
            source: source.try_into().unwrap(),
            target: target.try_into().unwrap(),
            color,
            expression,
            out_next: None,
            in_prev: None,
        }
    }

    /// Consumes `self` and applies the given function `f` to obtain a new color which is then
    /// combined with the remaining fields to form a recolored edge.
    pub fn recolor<D, F: Fn(C) -> D>(self, f: F) -> LinkedListTransitionSystemEdge<E, D> {
        LinkedListTransitionSystemEdge {
            out_prev: self.out_prev,
            source: self.source,
            target: self.target,
            color: f(self.color),
            expression: self.expression,
            out_next: self.out_next,
            in_next: self.in_next,
            in_prev: self.in_prev,
        }
    }
}

impl<E, C, I> PartialEq<(I, E, C, I)> for LinkedListTransitionSystemEdge<E, C>
where
    I: ScalarIndexType,
    E: PartialEq,
    C: PartialEq,
{
    fn eq(&self, other: &(I, E, C, I)) -> bool {
        self.source == other.0.into_usize()
            && self.expression == other.1
            && self.color == other.2
            && self.target == other.3.into_usize()
    }
}
impl<E, C, I> PartialEq<(I, E, C, I)> for &LinkedListTransitionSystemEdge<E, C>
where
    I: ScalarIndexType,
    E: PartialEq,
    C: PartialEq,
{
    fn eq(&self, other: &(I, E, C, I)) -> bool {
        self.source == other.0.into_usize()
            && self.expression == other.1
            && self.color == other.2
            && self.target == other.3.into_usize()
    }
}
impl<E, I, C> PartialEq<(I, E, I)> for LinkedListTransitionSystemEdge<E, C>
where
    I: ScalarIndexType,
    E: PartialEq,
{
    fn eq(&self, other: &(I, E, I)) -> bool {
        self.source == other.0.into_usize()
            && self.expression == other.1
            && self.target == other.2.into_usize()
    }
}
impl<E, I> PartialEq<(I, E, I)> for &LinkedListTransitionSystemEdge<E, Void>
where
    I: ScalarIndexType,
    E: PartialEq,
{
    fn eq(&self, other: &(I, E, I)) -> bool {
        self.source == other.0.into_usize()
            && self.expression == other.1
            && self.target == other.2.into_usize()
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool>
    IntoEdgeTuple<LinkedListTransitionSystem<A, Q, C, DET>>
    for LinkedListTransitionSystemEdge<A::Expression, C>
{
    fn into_edge_tuple(self) -> crate::ts::EdgeTuple<LinkedListTransitionSystem<A, Q, C, DET>> {
        (
            self.source.try_into().unwrap(),
            self.expression.clone(),
            self.color.clone(),
            self.target.try_into().unwrap(),
        )
    }
}

impl<'a, E, C: Clone> IsEdge<'a, E, DefaultIdType, C> for &'a LinkedListTransitionSystemEdge<E, C> {
    fn target(&self) -> DefaultIdType {
        self.target.try_into().unwrap()
    }

    fn color(&self) -> C {
        self.color.clone()
    }

    fn expression(&self) -> &'a E {
        &self.expression
    }

    fn source(&self) -> DefaultIdType {
        self.source.try_into().unwrap()
    }
}

impl<E: Debug, C: Debug> Debug for LinkedListTransitionSystemEdge<E, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "LinkedEdge {{ {} --{:?}|{:?}--> {}   out[{:?}|{:?}], in[{:?}|{:?}] }}",
            self.source,
            self.expression,
            self.color,
            self.target,
            self.out_prev,
            self.out_next,
            self.in_prev,
            self.in_next
        )
    }
}
