use crate::alphabet::{Alphabet, CharAlphabet, Directional, InvertibleChar, Matcher};
use crate::ts::{
    Deterministic, DeterministicEdgesFrom, EdgeColor, EdgeExpression, EdgeReference, StateColor,
    StateIndex, SymbolOf,
};
use crate::{Pointed, TransitionSystem};
use std::collections::BTreeMap;

use super::{Accumulates, RunProfile, TransitionMonoid};

/// Represents the two-sided Cayley graph of a deterministic transition system.
/// In essence, it is a graph using transition profiles of the ts as nodes. It uses
/// a [`Directional`] alphabet to represent concatenation both from the left and the right.
///
/// There are different ways of building the Cayley graph. The most important distinction
/// lies in how two colours are combined, which is determined through the [`Accumulates`] trait.
/// Specifically, the Cayley graph associates a finite word `w` with a transition profile `tp`
/// that describes the behaviour of `w` when applied to/read from any state of the transition system.
///
/// The transformation on the state itself is straightforward as the transition profile can simply
/// store which state is reached. However the encountered edge and state colours need to be taken
/// into account as well. The [`Accumulates`] trait provides a way to combine these colours.
///
/// Since the Cayley graph is merely a way of visualising the transition profiles/transition monoid
/// of a transition system, we defer for an example to [`TransitionMonoid`].
#[derive(Clone)]
pub struct Cayley<Ts: Deterministic<Alphabet = CharAlphabet> + Pointed>
where
    Ts::EdgeColor: Accumulates,
    Ts::StateColor: Accumulates,
{
    alphabet: Directional,
    expressions: Vec<InvertibleChar>,
    m: TransitionMonoid<Ts>,
}

/// The right Cayley graph of a deterministic transition system is a graph that uses
/// the transition profiles of the ts as nodes. See [`Cayley`] for more details.
#[derive(Clone)]
pub struct RightCayley<Ts: TransitionSystem + Pointed> {
    expressions: BTreeMap<SymbolOf<Ts>, EdgeExpression<Ts>>,
    m: TransitionMonoid<Ts>,
}

impl<Ts> Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    /// Returns a reference to the [`TransitionMonoid`].
    pub fn monoid(&self) -> &TransitionMonoid<Ts> {
        &self.m
    }
}

impl<Ts> TransitionSystem for Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    type StateIndex = usize;

    type StateColor = RunProfile<Ts::StateIndex, StateColor<Ts>, EdgeColor<Ts>>;

    type EdgeColor = ();

    type EdgeRef<'this>
        = EdgeReference<'this, InvertibleChar, usize, ()>
    where
        Self: 'this;

    type StateIndices<'this>
        = std::ops::Range<usize>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = DeterministicEdgesFrom<'this, Self>
    where
        Self: 'this;

    type Alphabet = Directional;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.monoid().profile_indices()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(DeterministicEdgesFrom::new(self, state))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.monoid().get_profile(state).map(|p| p.0.clone())
    }
}

impl<Ts> Deterministic for Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    fn edge(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Self::EdgeRef<'_>> {
        let expression = self.expressions.iter().find(|e| matcher.matches(e))?;
        let target = if expression.is_inverted() {
            self.m.left_successor(state, expression.symbol())?
        } else {
            self.m.right_successor(state, expression.symbol())?
        };
        Some(EdgeReference::new(state, expression, &(), target))
    }
}

impl<Ts> Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    Ts::EdgeColor: Accumulates,
    Ts::StateColor: Accumulates,
{
    /// Build a new Cayley graph from the given transition system.
    pub fn new(ts: Ts) -> Self {
        let m = TransitionMonoid::new(ts);
        Self::from_monoid(m)
    }
}

impl<Ts> Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    Ts::StateColor: Accumulates,
    Ts::EdgeColor: Accumulates,
{
    /// Builds a new Cayley graph from the given transition system and transition monoid.
    pub fn from(ts: Ts, m: TransitionMonoid<Ts>) -> Self {
        let _ = ts;
        Self::from_monoid(m)
    }

    fn from_monoid(m: TransitionMonoid<Ts>) -> Self {
        let alphabet = Directional::from_iter(m.ts().alphabet().universe());
        let expressions = alphabet.universe().collect();
        Self {
            alphabet,
            expressions,
            m,
        }
    }
}

impl<Ts> RightCayley<Ts>
where
    Ts: TransitionSystem + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    /// Returns a reference to the underlying ts.
    pub fn ts(&self) -> &Ts {
        self.m.ts()
    }

    /// Returns a reference to the [`TransitionMonoid`].
    pub fn monoid(&self) -> &TransitionMonoid<Ts> {
        &self.m
    }
}

impl<Ts> TransitionSystem for RightCayley<Ts>
where
    Ts: Deterministic + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    type StateIndex = usize;

    type StateColor = RunProfile<Ts::StateIndex, StateColor<Ts>, EdgeColor<Ts>>;

    type EdgeColor = ();

    type EdgeRef<'this>
        = EdgeReference<'this, EdgeExpression<Ts>, usize, ()>
    where
        Self: 'this;

    type StateIndices<'this>
        = std::ops::Range<usize>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = DeterministicEdgesFrom<'this, Self>
    where
        Self: 'this;

    type Alphabet = Ts::Alphabet;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts().alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.monoid().profile_indices()
    }
    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(DeterministicEdgesFrom::new(self, state))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.monoid().get_profile(state).map(|p| p.0.clone())
    }
}

impl<Ts> Deterministic for RightCayley<Ts>
where
    Ts: Deterministic + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    fn edge(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Self::EdgeRef<'_>> {
        let (symbol, expression) = self.expressions.iter().find(|(_, e)| matcher.matches(e))?;
        let target = self.m.right_successor(state, *symbol)?;
        Some(EdgeReference::new(state, expression, &(), target))
    }
}
impl<Ts> RightCayley<Ts>
where
    Ts: TransitionSystem + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    /// Builds a new right Cayley graph from the given transition monoid.
    pub fn from(m: TransitionMonoid<Ts>) -> Self {
        let expressions = m.ts().alphabet().expression_map();
        Self { expressions, m }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::{Builder, IsEdge};

    fn parity_dfa() -> crate::automaton::DFA {
        Builder::without_edge_colors()
            .with_state_colors([false, true])
            .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (1, 'b', 1)])
            .into_dfa(0)
    }

    #[test]
    fn right_cayley_edges() {
        let rc = RightCayley::from(TransitionMonoid::new(parity_dfa()));
        assert_eq!(rc.state_indices().count(), 5);
        assert_eq!(rc.edges_from(0).unwrap().count(), 2);
        assert_eq!(rc.size(), 5);
        for q in rc.state_indices() {
            for sym in ['a', 'b'] {
                let e = rc.edge(q, sym).unwrap();
                assert_eq!(e.target(), rc.monoid().right_successor(q, sym).unwrap());
            }
        }
        // the transition on 'a' from epsilon leads to the profile of "a"
        let a = rc.monoid().profile_for("a").unwrap();
        assert_eq!(rc.edge(0, 'a').unwrap().target(), a);
        assert_eq!(rc.edge(0, 'x'), None);
    }

    #[test]
    fn cayley_edges() {
        let c = Cayley::new(parity_dfa());
        assert_eq!(c.state_indices().count(), 5);
        assert_eq!(c.edges_from(0).unwrap().count(), 4);
        assert_eq!(c.size(), 5);
        let a = c.monoid().profile_for("a").unwrap();
        let right_a = c
            .alphabet()
            .universe()
            .find(|s| !s.is_inverted() && s.symbol() == 'a');
        let left_a = c
            .alphabet()
            .universe()
            .find(|s| s.is_inverted() && s.symbol() == 'a');
        assert_eq!(c.edge(0, right_a.unwrap()).unwrap().target(), a);
        assert_eq!(c.edge(0, left_a.unwrap()).unwrap().target(), a);
    }
}
