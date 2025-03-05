use crate::ts::IndexType;
use automata_core::Void;
use std::fmt::Debug;

/// This trait is implemented for references to transitions, so that they can be used in
/// generic contexts. It is automatically implemented for (mutable) references.
pub trait IsEdge<'ts, E, Idx, C> {
    /// Returns the index of the source state of the transition.
    fn source(&self) -> Idx;
    /// Returns the target state of the transition.
    fn target(&self) -> Idx;
    /// Returns the color of the transition.
    fn color(&self) -> C;
    /// Gives a reference to the expression that labels the transition.
    fn expression(&self) -> &'ts E;
    /// Destructures the transition into its components.
    fn into_tuple(self) -> (Idx, &'ts E, Idx, C)
    where
        Self: Sized,
    {
        (
            self.source(),
            self.expression(),
            self.target(),
            self.color(),
        )
    }

    /// Destructures `self` but into a slightly different form.
    fn into_nested_tuple(self) -> (Idx, &'ts E, (Idx, C))
    where
        Self: Sized,
    {
        (
            self.source(),
            self.expression(),
            (self.target(), self.color()),
        )
    }
}

/// Represents an edge that is not associated to a transition system. It stores a color, an
/// expression, as well as a source and target state index.
#[derive(Clone, Eq, PartialEq, Debug, Ord, PartialOrd, Hash)]
pub struct Edge<E, Idx, C> {
    source: Idx,
    target: Idx,
    color: C,
    expression: E,
}

impl<'a, E, Idx: Copy, C: Clone> IsEdge<'a, E, Idx, C> for &'a Edge<E, Idx, C> {
    fn target(&self) -> Idx {
        self.target
    }

    fn color(&self) -> C {
        self.color.clone()
    }

    fn expression(&self) -> &'a E {
        &self.expression
    }

    fn source(&self) -> Idx {
        self.source
    }
}

impl<E, Idx, C> Edge<E, Idx, C> {
    /// Creates a new edge with the given source, expression, color and target.
    pub fn new(source: Idx, expression: E, color: C, target: Idx) -> Self {
        Self {
            source,
            target,
            color,
            expression,
        }
    }
}

/// Represents a reference to an edge in a transition system. This stores a lifetime
/// to the transition system and references to the color and expression.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialOrd, Ord, PartialEq)]
pub struct EdgeReference<'ts, E, Idx, C> {
    source: Idx,
    target: Idx,
    color: &'ts C,
    expression: &'ts E,
}

impl<E: Eq, Idx: IndexType, C: Clone + Eq> PartialEq<(Idx, E, C, Idx)>
    for EdgeReference<'_, E, Idx, C>
{
    fn eq(&self, other: &(Idx, E, C, Idx)) -> bool {
        self.source == other.0
            && self.target == other.3
            && self.color == &other.2
            && self.expression == &other.1
    }
}

impl<E: Eq, Idx: IndexType> PartialEq<(Idx, E, Idx)> for EdgeReference<'_, E, Idx, Void> {
    fn eq(&self, other: &(Idx, E, Idx)) -> bool {
        self.source == other.0 && self.target == other.2 && self.expression == &other.1
    }
}

impl<'ts, E, Idx, C> EdgeReference<'ts, E, Idx, C> {
    /// Creates a new edge reference from the given components.
    pub fn new(source: Idx, expression: &'ts E, color: &'ts C, target: Idx) -> Self {
        Self {
            source,
            target,
            color,
            expression,
        }
    }
}

impl<'ts, E, Idx: IndexType, C: Clone> IsEdge<'ts, E, Idx, C> for EdgeReference<'ts, E, Idx, C> {
    fn source(&self) -> Idx {
        self.source
    }

    fn target(&self) -> Idx {
        self.target
    }

    fn color(&self) -> C {
        self.color.clone()
    }

    fn expression(&self) -> &'ts E {
        self.expression
    }
}

/// Represents an edge in a transition system similar to [`EdgeReference`], but it owns the
/// associated color, while the expression is still a reference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TransitionOwnedColor<'ts, E, Idx, C> {
    source: Idx,
    target: Idx,
    color: C,
    expression: &'ts E,
}

impl<'ts, E, Idx, C> TransitionOwnedColor<'ts, E, Idx, C> {
    /// Creates a new instance from the given components.
    pub fn new(source: Idx, expression: &'ts E, color: C, target: Idx) -> Self {
        Self {
            source,
            target,
            color,
            expression,
        }
    }
}

impl<'ts, E, Idx: IndexType, C: Clone> IsEdge<'ts, E, Idx, C>
    for TransitionOwnedColor<'ts, E, Idx, C>
{
    fn source(&self) -> Idx {
        self.source
    }

    fn target(&self) -> Idx {
        self.target
    }

    fn color(&self) -> C {
        self.color.clone()
    }

    fn expression(&self) -> &'ts E {
        self.expression
    }
}
