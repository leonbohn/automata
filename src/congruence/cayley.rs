use crate::{prelude::*, transition_system::EdgeReference};

use self::alphabet::{Directional, InvertibleChar};

use super::{
    transitionprofile::{Reduces, Replaces},
    Accumulates, RunProfile, TransitionMonoid,
};

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
/// There are two main ways to combine the colours:
/// - `Reduces`: This struct takes the minimum of the currently stored/known and any encountered value.
/// - `Replaces`: This struct stores any encountered value and replaces the currently stored value.
/// - `Collect` (not yet implemented): This struct collects all encountered values.
#[derive(Clone)]
pub struct Cayley<
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    SA: Accumulates<X = Ts::StateColor>,
    EA: Accumulates<X = Ts::EdgeColor>,
> {
    alphabet: Directional,
    expressions: crate::Map<SymbolOf<Self>, ExpressionOf<Self>>,
    m: TransitionMonoid<Ts, SA, EA>,
}

/// The right Cayley graph of a deterministic transition system is a graph that uses
/// the transition profiles of the ts as nodes. See [`Cayley`] for more details.
#[derive(Clone)]
pub struct RightCayley<
    Ts: TransitionSystem + Pointed,
    SA: Accumulates<X = Ts::StateColor>,
    EA: Accumulates<X = Ts::EdgeColor>,
> {
    expressions: crate::Map<SymbolOf<Ts>, ExpressionOf<Ts>>,
    m: TransitionMonoid<Ts, SA, EA>,
}

impl<
        Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
        SA: Accumulates<X = Ts::StateColor>,
        EA: Accumulates<X = Ts::EdgeColor>,
    > Cayley<Ts, SA, EA>
{
    /// Returns a reference to the [`TransitionMonoid`].
    pub fn monoid(&self) -> &TransitionMonoid<Ts, SA, EA> {
        &self.m
    }
}

impl<Ts, SA: Accumulates<X = Ts::StateColor>, EA: Accumulates<X = Ts::EdgeColor>> TransitionSystem
    for Cayley<Ts, SA, EA>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
{
    type StateIndex = usize;

    type StateColor = RunProfile<Ts::StateIndex, SA, EA>;

    type EdgeColor = ();

    type EdgeRef<'this> = EdgeReference<'this, InvertibleChar, usize, ()> where Self: 'this;

    type StateIndices<'this> = std::ops::Range<usize> where Self: 'this;

    type EdgesFromIter<'this> = DeterministicEdgesFrom<'this, Self> where Self: 'this;

    type Alphabet = Directional;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.monoid().profile_indices()
    }

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        Some(DeterministicEdgesFrom::new(self, state.to_index(self)?))
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        self.monoid()
            .get_profile(state.to_index(self)?)
            .map(|p| p.0.clone())
    }
}

impl<Ts, SA: Accumulates<X = Ts::StateColor>, EA: Accumulates<X = Ts::EdgeColor>> Deterministic
    for Cayley<Ts, SA, EA>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
{
    fn transition<Idx: Indexes<Self>>(
        &self,
        state: Idx,
        symbol: SymbolOf<Self>,
    ) -> Option<Self::EdgeRef<'_>> {
        let idx = state.to_index(self)?;
        let (_tp, string) = self.monoid().get_profile(idx)?;
        let mut word = string.to_deque();
        symbol.mul(&mut word);
        let tp = self.monoid().profile_for(&word)?;
        Some(EdgeReference::new(
            idx,
            self.expressions.get(&symbol).unwrap(),
            &(),
            tp,
        ))
    }
}

impl<Ts> Cayley<Ts, Reduces<Ts::StateColor>, Reduces<Ts::EdgeColor>>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    Reduces<Ts::EdgeColor>: Accumulates<X = Ts::EdgeColor>,
    Reduces<Ts::StateColor>: Accumulates<X = Ts::StateColor>,
{
    /// Instantiates a new Cayley graph that reduces the state and edge colors. Specifically,
    /// this means that the state and edge colors are accumulated by taking the minimum of the
    /// currently stored/known and any encountered value.
    pub fn new_reducing(ts: Ts) -> Self {
        let alphabet = Directional::from_iter(ts.alphabet().universe());
        Cayley {
            expressions: alphabet.expression_map(),
            m: TransitionMonoid::new_reducing(ts),
            alphabet,
        }
    }
}
impl<Ts> Cayley<Ts, Replaces<Ts::StateColor>, Replaces<Ts::EdgeColor>>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    Replaces<Ts::EdgeColor>: Accumulates<X = Ts::EdgeColor>,
    Replaces<Ts::StateColor>: Accumulates<X = Ts::StateColor>,
{
    /// Instantiates a new Cayley graph that replaces the state and edge colors. This means
    /// any encountered value is stored and replaces the currently stored value.
    pub fn new_replacing(ts: Ts) -> Self {
        let alphabet = Directional::from_iter(ts.alphabet().universe());
        Cayley {
            expressions: alphabet.expression_map(),
            alphabet,
            m: TransitionMonoid::new_replacing(ts),
        }
    }
}

impl<Ts, SA: Accumulates<X = Ts::StateColor>, EA: Accumulates<X = Ts::EdgeColor>> Cayley<Ts, SA, EA>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    Ts::StateColor: Accumulates,
    Ts::EdgeColor: Accumulates,
{
    /// Builds a new Cayley graph from the given transition system and transition monoid.
    pub fn from(ts: Ts, m: TransitionMonoid<Ts, SA, EA>) -> Self {
        let alphabet = Directional::from_iter(ts.alphabet().universe());
        Self {
            expressions: alphabet.expression_map(),
            alphabet,
            m,
        }
    }
}

impl<
        Ts: TransitionSystem + Pointed,
        SA: Accumulates<X = Ts::StateColor>,
        EA: Accumulates<X = Ts::EdgeColor>,
    > RightCayley<Ts, SA, EA>
{
    /// Returns a reference to the underlying ts.
    pub fn ts(&self) -> &Ts {
        self.m.ts()
    }

    /// Returns a reference to the [`TransitionMonoid`].
    pub fn monoid(&self) -> &TransitionMonoid<Ts, SA, EA> {
        &self.m
    }
}

impl<Ts, SA: Accumulates<X = Ts::StateColor>, EA: Accumulates<X = Ts::EdgeColor>> TransitionSystem
    for RightCayley<Ts, SA, EA>
where
    Ts: Deterministic + Pointed,
{
    type StateIndex = usize;

    type StateColor = RunProfile<Ts::StateIndex, SA, EA>;

    type EdgeColor = ();

    type EdgeRef<'this> = EdgeReference<'this, ExpressionOf<Ts>, usize, ()> where Self: 'this;

    type StateIndices<'this> = std::ops::Range<usize> where Self: 'this;

    type EdgesFromIter<'this> = DeterministicEdgesFrom<'this, Self> where Self: 'this;

    type Alphabet = Ts::Alphabet;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts().alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.monoid().profile_indices()
    }
    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        Some(DeterministicEdgesFrom::new(self, state.to_index(self)?))
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        self.monoid()
            .get_profile(state.to_index(self)?)
            .map(|p| p.0.clone())
    }
}

impl<Ts, SA: Accumulates<X = Ts::StateColor>, EA: Accumulates<X = Ts::EdgeColor>> Deterministic
    for RightCayley<Ts, SA, EA>
where
    Ts: Deterministic + Pointed,
{
    fn transition<Idx: Indexes<Self>>(
        &self,
        state: Idx,
        symbol: SymbolOf<Self>,
    ) -> Option<Self::EdgeRef<'_>> {
        let idx = state.to_index(self)?;
        let (_tp, string) = self.monoid().get_profile(idx)?;
        let mut word = string.to_vec();
        word.push(symbol);
        let tp = self.monoid().profile_for(&word)?;
        Some(EdgeReference::new(
            idx,
            self.expressions.get(&symbol).unwrap(),
            &(),
            tp,
        ))
    }
}

impl<Ts> RightCayley<Ts, Reduces<Ts::StateColor>, Reduces<Ts::EdgeColor>>
where
    Ts: Deterministic + Pointed,
    Reduces<Ts::EdgeColor>: Accumulates<X = Ts::EdgeColor>,
    Reduces<Ts::StateColor>: Accumulates<X = Ts::StateColor>,
{
    /// Instantiates a new right Cayley graph that reduces the state and edge colors. Specifically,
    /// this means that the state and edge colors are accumulated by taking the minimum of the currently
    /// stored/known and any encountered value.
    pub fn new_reducing(ts: Ts) -> Self {
        RightCayley {
            expressions: ts.alphabet().expression_map(),
            m: TransitionMonoid::new_reducing(ts),
        }
    }
}
impl<Ts> RightCayley<Ts, Replaces<Ts::StateColor>, Replaces<Ts::EdgeColor>>
where
    Ts: Deterministic + Pointed,
    Replaces<Ts::EdgeColor>: Accumulates<X = Ts::EdgeColor>,
    Replaces<Ts::StateColor>: Accumulates<X = Ts::StateColor>,
{
    /// Instantiates a new right Cayley graph that replaces the state and edge colors. This means
    /// any encountered value is stored and replaces the currently stored value.
    pub fn new_replacing(ts: Ts) -> Self {
        RightCayley {
            expressions: ts.alphabet().expression_map(),
            m: TransitionMonoid::new_replacing(ts),
        }
    }
}

impl<Ts, SA: Accumulates<X = Ts::StateColor>, EA: Accumulates<X = Ts::EdgeColor>>
    RightCayley<Ts, SA, EA>
where
    Ts: TransitionSystem + Pointed,
    Ts::StateColor: Accumulates,
    Ts::EdgeColor: Accumulates,
{
    /// Builds a new right Cayley graph from the given transition system and transition monoid.
    pub fn from(ts: Ts, m: TransitionMonoid<Ts, SA, EA>) -> Self {
        Self {
            expressions: ts.alphabet().expression_map(),
            m,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::tests::wiki_dfa;

    #[test]
    #[ignore]
    fn right_cayley_graph() {
        let dfa = wiki_dfa();
        let _accumulating_cayley = super::Cayley::new_reducing(&dfa);
        let _replacing_cayley = super::Cayley::new_replacing(&dfa);
        todo!("Find something to test?")
    }
}
