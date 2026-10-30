use std::borrow::Cow;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

/// A reference to an edge of a transition system. This is the single edge type that
/// [`crate::TransitionSystem::edges_from`] and [`crate::ts::PredecessorIterable::predecessors`] yield, for
/// storages and for adapters alike. The expression is borrowed from the system, the color is
/// borrowed if it is stored and owned if it is computed (for example by a recoloring adapter or a
/// product).
///
/// For predecessors, `source` is the state the edge comes from and `target` the state that was
/// asked for, so the fields always describe the direction of the edge itself.
#[derive(Clone, Debug)]
pub struct EdgeRef<'a, I, E, C: Clone> {
    source: I,
    target: I,
    expression: &'a E,
    color: Cow<'a, C>,
}

impl<I: PartialEq, E: PartialEq, C: Clone + PartialEq> PartialEq for EdgeRef<'_, I, E, C> {
    fn eq(&self, other: &Self) -> bool {
        self.source == other.source
            && self.target == other.target
            && self.expression == other.expression
            && self.color == other.color
    }
}
impl<I: Eq, E: Eq, C: Clone + Eq> Eq for EdgeRef<'_, I, E, C> {}
impl<I: Hash, E: Hash, C: Clone + Hash> Hash for EdgeRef<'_, I, E, C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.source.hash(state);
        self.target.hash(state);
        self.expression.hash(state);
        self.color.hash(state);
    }
}
impl<I: PartialOrd, E: PartialOrd, C: Clone + PartialOrd> PartialOrd for EdgeRef<'_, I, E, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (&self.source, &self.target, self.expression, &self.color).partial_cmp(&(
            &other.source,
            &other.target,
            other.expression,
            &other.color,
        ))
    }
}
impl<I: Ord, E: Ord, C: Clone + Ord> Ord for EdgeRef<'_, I, E, C> {
    fn cmp(&self, other: &Self) -> Ordering {
        (&self.source, &self.target, self.expression, &self.color).cmp(&(
            &other.source,
            &other.target,
            other.expression,
            &other.color,
        ))
    }
}

impl<'a, I, E, C: Clone> EdgeRef<'a, I, E, C> {
    /// Creates a new edge reference from the given components.
    #[inline(always)]
    pub fn new(source: I, expression: &'a E, color: Cow<'a, C>, target: I) -> Self {
        Self {
            source,
            target,
            expression,
            color,
        }
    }

    /// Creates an edge reference that borrows its color.
    #[inline(always)]
    pub fn borrowed(source: I, expression: &'a E, color: &'a C, target: I) -> Self {
        Self::new(source, expression, Cow::Borrowed(color), target)
    }

    /// Creates an edge reference that owns its color.
    #[inline(always)]
    pub fn owned(source: I, expression: &'a E, color: C, target: I) -> Self {
        Self::new(source, expression, Cow::Owned(color), target)
    }

    /// Returns the source state of the edge.
    #[inline(always)]
    pub fn source(&self) -> I
    where
        I: Copy,
    {
        self.source
    }

    /// Returns the target state of the edge.
    #[inline(always)]
    pub fn target(&self) -> I
    where
        I: Copy,
    {
        self.target
    }

    /// Returns a reference to the expression that labels the edge.
    #[inline(always)]
    pub fn expression(&self) -> &'a E {
        self.expression
    }

    /// Returns a reference to the color of the edge.
    #[inline(always)]
    pub fn color(&self) -> &C {
        &self.color
    }

    /// Consumes the edge and returns its color, which is only cloned if it is not owned yet.
    #[inline(always)]
    pub fn into_color(self) -> Cow<'a, C> {
        self.color
    }

    /// Returns the edge with source and target exchanged.
    #[inline(always)]
    pub fn reversed(self) -> Self {
        Self {
            source: self.target,
            target: self.source,
            ..self
        }
    }

    /// Returns the edge with the same source, target and expression but the given color.
    #[inline(always)]
    pub fn with_color<D: Clone>(self, color: Cow<'a, D>) -> EdgeRef<'a, I, E, D> {
        EdgeRef {
            source: self.source,
            target: self.target,
            expression: self.expression,
            color,
        }
    }

    /// Returns the edge with the source and target replaced by `f`.
    #[inline(always)]
    pub fn map_states<J>(self, mut f: impl FnMut(I) -> J) -> EdgeRef<'a, J, E, C> {
        EdgeRef {
            source: f(self.source),
            target: f(self.target),
            expression: self.expression,
            color: self.color,
        }
    }

    /// Destructures the edge into the owned tuple `(source, expression, color, target)`, cloning
    /// the expression.
    #[inline(always)]
    pub fn into_tuple(self) -> (I, E, C, I)
    where
        E: Clone,
    {
        (
            self.source,
            self.expression.clone(),
            self.color.into_owned(),
            self.target,
        )
    }
}

impl<I: PartialEq, E: PartialEq, C: Clone + PartialEq> PartialEq<(I, E, C, I)>
    for EdgeRef<'_, I, E, C>
{
    fn eq(&self, other: &(I, E, C, I)) -> bool {
        self.source == other.0
            && self.target == other.3
            && *self.color == other.2
            && *self.expression == other.1
    }
}

impl<I: PartialEq, E: PartialEq> PartialEq<(I, E, I)> for EdgeRef<'_, I, E, crate::Void> {
    fn eq(&self, other: &(I, E, I)) -> bool {
        self.source == other.0 && self.target == other.2 && *self.expression == other.1
    }
}
