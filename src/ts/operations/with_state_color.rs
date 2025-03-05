use crate::core::{Color, math};
use crate::ts::{Deterministic, StateIndex};
use crate::{Pointed, TransitionSystem};
use std::hash::Hash;

/// Implementors of this trait provide a color for states of a
/// [`TransitionSystem`] that are indexed by the type `Idx` and
/// the output color is given by the associated type `Color`.
///
/// Naturally, a color itself provides a state color, namely by
/// associating each state with itself. Similarly, a [`math::Map`]
/// using `Idx` as key and `Color` as value provides a color for
/// each state, provided it is complete (in the sense that it has
/// an entry for each state index). Finally, it is possible to
/// extend an incomplete Map by providing a default color for
/// missing entries through the [`DefaultIfMissing`] struct.
pub trait ProvidesStateColor<Idx> {
    /// The output color given to each state.
    type Color: Color;
    /// Returns the color assigned to the given `state`. Note,
    /// that the trait is assumed to provide a complete coloring,
    /// which means the method must return a color for every
    /// possible `Idx` that is provided. Consequently, it may
    /// panic if the coloring is not complete.
    fn state_color(&self, state: Idx) -> Self::Color;
}

/// Provides a uniform color for all states of a [`TransitionSystem`]. The main use case for
/// this struct is when calling [`TransitionSystem::with_state_color`] and providing a single
/// color for all states.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct UniformColor<C: Color>(pub C);

impl<Idx, C: Color> ProvidesStateColor<Idx> for UniformColor<C> {
    type Color = C;
    fn state_color(&self, _state: Idx) -> Self::Color {
        self.0.clone()
    }
}

impl<Idx: Hash + Eq, C: Color> ProvidesStateColor<Idx> for math::Map<Idx, C> {
    type Color = C;

    fn state_color(&self, state: Idx) -> Self::Color {
        self.get(&state)
            .cloned()
            .expect("Need a color for this state!")
    }
}

impl<Idx, C: Color, F: Fn(Idx) -> C> ProvidesStateColor<Idx> for F {
    type Color = C;
    fn state_color(&self, state: Idx) -> Self::Color {
        (self)(state)
    }
}

/// Augments a [`math::Map`] with a default color for missing
/// entries. This struct implements [`ProvidesStateColor`] and
/// wrapping an incomplete map is its only purpose.
///
/// Specifically, it returns the color stored in the [`math::Map`]
/// it wraps for a `state` if present and the stored `default`
/// value otherwise.
#[derive(Clone, Eq, PartialEq)]
pub struct DefaultIfMissing<X: Hash + Eq, Y> {
    map: math::Map<X, Y>,
    default: Y,
}

impl<X: Hash + Eq, Y: Color> DefaultIfMissing<X, Y> {
    /// Creates a new instance of `Self` from a given (partial)
    /// map and default value.
    pub fn new(map: math::Map<X, Y>, default: Y) -> Self {
        Self { map, default }
    }
}

impl<Idx: Hash + Eq, Y: Color> ProvidesStateColor<Idx> for DefaultIfMissing<Idx, Y> {
    type Color = Y;

    fn state_color(&self, state: Idx) -> Self::Color {
        self.map
            .get(&state)
            .cloned()
            .unwrap_or(self.default.clone())
    }
}

/// Wraps a [`TransitionSystem`] and replaces the colors on its
/// states by the ones provided by a [`ProvidesStateColor`]
/// instance.
#[derive(Clone, Eq, PartialEq)]
pub struct WithStateColor<Ts: TransitionSystem, P: ProvidesStateColor<Ts::StateIndex>> {
    ts: Ts,
    provider: P,
}

impl<Ts: Pointed, P: ProvidesStateColor<Ts::StateIndex>> Pointed for WithStateColor<Ts, P> {
    fn initial(&self) -> Self::StateIndex {
        self.ts.initial()
    }
}

impl<Ts: Deterministic, P: ProvidesStateColor<Ts::StateIndex>> Deterministic
    for WithStateColor<Ts, P>
{
}

impl<Ts: TransitionSystem, P: ProvidesStateColor<Ts::StateIndex>> TransitionSystem
    for WithStateColor<Ts, P>
{
    type Alphabet = Ts::Alphabet;

    type StateIndex = Ts::StateIndex;

    type StateColor = P::Color;

    type EdgeColor = Ts::EdgeColor;

    type EdgeRef<'this>
        = Ts::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = Ts::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this>
        = Ts::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.ts.state_indices()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        self.ts.edges_from(state)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        let idx = state;
        Some(self.provider.state_color(idx))
    }
}

impl<Ts: TransitionSystem, P: ProvidesStateColor<Ts::StateIndex>> WithStateColor<Ts, P> {
    /// Creates a new instance of `Self` from a [`TransitionSystem`]
    /// and an instance of [`ProvidesStateColor`] that is used to
    /// recolor the states of the ts.
    pub fn new(ts: Ts, provider: P) -> Self {
        Self { ts, provider }
    }

    /// Decomposes `self` into its constituent parts.
    pub fn into_parts(self) -> (Ts, P) {
        (self.ts, self.provider)
    }
}
