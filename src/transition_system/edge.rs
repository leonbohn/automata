use crate::prelude::*;

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

/// Represents a reference to an edge in a transition system. This stores a lifetime
/// to the transition system and references to the color and expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EdgeReference<'ts, E, Idx, C> {
    source: Idx,
    target: Idx,
    color: &'ts C,
    expression: &'ts E,
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
