use std::hash::Hash;

use crate::prelude::*;

pub trait ProvidesStateColor<Idx> {
    type Color: Color;
    fn state_color(&self, state: Idx) -> Self::Color;
}

impl<Idx, C: Color> ProvidesStateColor<Idx> for C {
    type Color = C;
    fn state_color(&self, state: Idx) -> Self::Color {
        self.clone()
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

#[derive(Clone, Eq, PartialEq)]
pub struct DefaultIfMissing<X: Hash + Eq, Y> {
    map: math::Map<X, Y>,
    default: Y,
}

impl<X: Hash + Eq, Y: Color> DefaultIfMissing<X, Y> {
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

    type EdgeRef<'this> = Ts::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this> = Ts::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this> = Ts::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.ts.state_indices()
    }

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        todo!()
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        let idx = state.to_index(self)?;
        Some(self.provider.state_color(idx))
    }
}

impl<Ts: TransitionSystem, P: ProvidesStateColor<Ts::StateIndex>> WithStateColor<Ts, P> {
    pub fn new(ts: Ts, provider: P) -> Self {
        Self { ts, provider }
    }
}
