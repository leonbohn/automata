use crate::prelude::*;

mod acceptance_type;
pub use acceptance_type::OmegaAcceptanceType;

#[macro_use]
mod moore;
pub use moore::{IntoMooreMachine, MooreMachine};

#[macro_use]
mod mealy;
pub use mealy::{IntoMealyMachine, MealyMachine};

mod dfa;
pub use dfa::{IntoDFA, DFA};

mod dpa;
pub use dpa::{IntoDPA, MinEven, DPA};

mod dba;
pub use dba::{IntoDBA, DBA};

#[allow(missing_docs)]
mod omega;
pub use omega::{
    AcceptanceMask, DeterministicOmegaAutomaton, OmegaAcceptanceCondition, OmegaAutomaton,
};

mod with_initial;
pub use with_initial::Initialized;

/// This module defines different types of _semantics_ that are used by the
/// [`Automaton`] struct for determining the output of a finite or infinite
/// run. This can either be some arbitrary output in the case of a Moore or
/// Mealy machine, or it would be a boolean indicating whether the input is
/// accepted or not in case of an acceptor like a DFA.
///
/// Generally, we distinguish between an [`Automaton`] of finite and one of
/// infinite words. The purpose of a semantic is to determine what to do
/// with the run that is induced by an input on some transition system.
///
/// # Finite inputs
/// For a finite input such as a [`FiniteWord`] we use [`FiniteSemantics`],
/// which defines an `Output` type and provides the [`FininiteSemantics::finite_semantic`] method.
/// It takes the [`FiniteRun`] that is the result of running the finite
/// input in some transition system and turns it into the desired output.
///
/// Examples of this semantic are for example the [`MooreSemantics`], which
/// for a finite word `w` simply produce the color of the state that is
/// reached when running `w` in the transition system from the initial state.
/// This is similar to the [`DFASemantics`], which additionaly demand that
/// the state colors are `bool`.
/// Further, there is also the [`MealySemantics`], which outputs the last
/// transition that is taken when reading `w`.
///
/// # Infinite inputs
/// For an infinite input like an [`OmegaWord`], we also need to define an
/// `Output` type. This is now computed in the [`omega_semantic`] method on
/// the [`OmegaSemantics`] trait. It does this based on an [`OmegaRun`].
///
/// Examples include the [`DBASemantics`], which may be applied to `bool`
/// edge-colored transition systems. It outputs `true` if any edge labeled
/// with `true` is visited infinitely often and `false` otherwise.
/// This can actually be viewed as an instantiation of the [`MinEven`]
/// semantics that a [`DPA`] uses, which outputs the least priority/color
/// among those that are labels of edges taken infinitely often.
pub mod semantics;
pub use semantics::{FiniteSemantics, OmegaSemantics};

/// An automaton consists of a transition system and an acceptance condition.
/// There are many different types of automata, which can be instantiated from
/// this struct by setting the type parameters accordingly.
///
/// The const parameter `OMEGA` determines whether the input type of the automaton
/// is finite or omega words. If `OMEGA` is `true`, the automaton accepts omega
/// words, otherwise it accepts finite words.
///
/// The type parameter `D` is the type of the transition system, and `A` is the
/// type of the acceptance condition.
///
/// In order for the automaton to be able to accept words, the acceptance condition
/// must implement the [`FiniteSemantics`] or [`OmegaSemantics`] trait, depending on
/// the value of `OMEGA` (in the former case `OMEGA` should be false, and in the
/// latter case `OMEGA` should be true).
#[derive(Clone, Eq, PartialEq, Copy)]
pub struct Automaton<D: TransitionSystem, A, const OMEGA: bool = false> {
    ts: D,
    initial: D::StateIndex,
    acceptance: A,
}

impl<D, A, const OMEGA: bool> Automaton<D, A, OMEGA>
where
    D: TransitionSystem<Alphabet = CharAlphabet>,
{
    /// Instantiates a new [`TSBuilder`] for the edge and state color of `self`.
    pub fn builder() -> TSBuilder<D::StateColor, D::EdgeColor> {
        TSBuilder::default()
    }
}

impl<D: TransitionSystem, A, const OMEGA: bool> Automaton<D, A, OMEGA> {
    /// Creates a new automaton from the given transition system and acceptance condition.
    pub fn from_parts(ts: D, initial: impl Indexes<D>, acceptance: A) -> Self {
        Self {
            initial: initial.to_index(&ts).unwrap(),
            ts,
            acceptance,
        }
    }

    /// Decomposes the automaton into its parts: the transition system and the acceptance condition.
    pub fn into_parts(self) -> (D, A) {
        (self.ts, self.acceptance)
    }

    /// Returns a reference to the underlying transition system.
    pub fn ts(&self) -> &D {
        &self.ts
    }

    /// Gives a mutable reference to the underlying transition system.
    pub fn ts_mut(&mut self) -> &mut D {
        &mut self.ts
    }

    /// Returns a reference to the acceptance condition.
    pub fn acceptance(&self) -> &A {
        &self.acceptance
    }
}

impl<D, A> Automaton<D, A, false>
where
    D: Congruence,
    A: FiniteSemantics<StateColor<D>, EdgeColor<D>>,
{
    /// Returns whether the automaton accepts the given finite word.
    pub fn accepts<W: FiniteWord<SymbolOf<D>>>(&self, word: W) -> bool
    where
        A: FiniteSemantics<StateColor<D>, EdgeColor<D>, Output = bool>,
    {
        self.transform(word)
    }

    /// Transforms the given finite word using the automaton, that means it returns
    /// the output of the acceptance condition on the run of the word.
    pub fn transform<W: FiniteWord<SymbolOf<D>>>(&self, word: W) -> A::Output {
        self.acceptance.finite_semantic(self.ts.finite_run(word))
    }
}

impl<D, A> Automaton<D, A, true>
where
    D: Congruence,
    A: OmegaSemantics<StateColor<D>, EdgeColor<D>>,
{
    /// Returns whether the automaton accepts the given omega word.
    pub fn accepts<W: OmegaWord<SymbolOf<D>>>(&self, word: W) -> bool
    where
        A: OmegaSemantics<StateColor<D>, EdgeColor<D>, Output = bool>,
    {
        self.acceptance.omega_semantic(self.ts.omega_run(word))
    }

    /// Transforms the given omega word using the automaton, that means it returns
    /// the output of the acceptance condition on the run of the word.
    pub fn transform<W: OmegaWord<SymbolOf<D>>>(&self, word: W) -> A::Output {
        self.acceptance.omega_semantic(self.ts.omega_run(word))
    }
}

impl<D: TransitionSystem, A, const OMEGA: bool> AsRef<Automaton<D, A, OMEGA>>
    for Automaton<D, A, OMEGA>
{
    fn as_ref(&self) -> &Automaton<D, A, OMEGA> {
        self
    }
}

impl<D: Deterministic, A, const OMEGA: bool> Deterministic for Automaton<D, A, OMEGA> {}

impl<D: PredecessorIterable, A, const OMEGA: bool> PredecessorIterable for Automaton<D, A, OMEGA> {
    type PreEdgeRef<'this> = D::PreEdgeRef<'this>
    where
        Self: 'this;

    type EdgesToIter<'this> = D::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        self.ts.predecessors(state.to_index(self)?)
    }
}

impl<D: TransitionSystem, A, const OMEGA: bool> Pointed for Automaton<D, A, OMEGA> {
    fn initial(&self) -> Self::StateIndex {
        self.initial
    }
}

impl<D: Sproutable, A: Default, const OMEGA: bool> Sproutable for Automaton<D, A, OMEGA>
where
    D::StateColor: Default,
{
    fn new_for_alphabet(alphabet: Self::Alphabet) -> Self {
        let mut ts = D::new_for_alphabet(alphabet);
        let initial = ts.add_state::<StateColor<D>>(Default::default());
        Automaton::from_parts(ts, initial, Default::default())
    }

    fn add_state<X: Into<StateColor<Self>>>(&mut self, color: X) -> Self::StateIndex {
        self.ts.add_state(color)
    }

    type ExtendStateIndexIter = D::ExtendStateIndexIter;

    fn extend_states<I: IntoIterator<Item = StateColor<Self>>>(
        &mut self,
        iter: I,
    ) -> Self::ExtendStateIndexIter {
        self.ts.extend_states(iter)
    }
    fn set_state_color<Idx: Indexes<Self>, X: Into<StateColor<Self>>>(
        &mut self,
        index: Idx,
        color: X,
    ) {
        self.ts.set_state_color(
            index
                .to_index(self)
                .expect("cannot set color of state that does not exist"),
            color,
        )
    }
    fn add_edge<X, Y, CI>(
        &mut self,
        from: X,
        on: <Self::Alphabet as Alphabet>::Expression,
        to: Y,
        color: CI,
    ) -> Option<(Self::StateIndex, Self::EdgeColor)>
    where
        X: Indexes<Self>,
        Y: Indexes<Self>,
        CI: Into<EdgeColor<Self>>,
    {
        let from = from.to_index(self)?;
        let to = to.to_index(self)?;
        self.ts.add_edge(from, on, to, color.into())
    }

    fn remove_edges<X: Indexes<Self>>(
        &mut self,
        from: X,
        on: <Self::Alphabet as Alphabet>::Expression,
    ) -> bool {
        let Some(from) = from.to_index(self) else {
            return false;
        };
        self.ts.remove_edges(from, on)
    }
}

impl<D: TransitionSystem, A, const OMEGA: bool> TransitionSystem for Automaton<D, A, OMEGA> {
    type Alphabet = D::Alphabet;

    type StateIndex = D::StateIndex;

    type StateColor = D::StateColor;

    type EdgeColor = D::EdgeColor;

    type EdgeRef<'this> = D::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this> = D::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this> = D::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.ts.state_indices()
    }

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        self.ts.edges_from(state.to_index(self)?)
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        self.ts.state_color(state.to_index(self)?)
    }
}

impl<T: TransitionSystem, A, const OMEGA: bool> std::fmt::Debug for Automaton<T, A, OMEGA>
where
    T: std::fmt::Debug,
    A: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}\nacceptance\t\t{:?}\n{:?}",
            match OMEGA {
                true => "Omega word automaton",
                false => "Finite word automaton",
            },
            self.acceptance,
            self.ts
        )
    }
}

/// Iterator over the accepting states of a [`TransitionSystem`] that have a certain coloring.
pub struct StatesWithColor<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    iter: Ts::StateIndices<'a>,
    color: Ts::StateColor,
}

impl<'a, Ts: TransitionSystem> StatesWithColor<'a, Ts> {
    /// Creates a new instance for the given transition system and color.
    pub fn new(ts: &'a Ts, color: Ts::StateColor) -> Self {
        Self {
            iter: ts.state_indices(),
            ts,
            color,
        }
    }
}

impl<'a, Ts: TransitionSystem> Clone for StatesWithColor<'a, Ts> {
    fn clone(&self) -> Self {
        Self {
            ts: self.ts,
            iter: self.ts.state_indices(),
            color: self.color.clone(),
        }
    }
}

impl<'a, Ts: TransitionSystem<StateColor = bool>> Iterator for StatesWithColor<'a, Ts> {
    type Item = Ts::StateIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .find(|&index| self.ts.state_color(index).unwrap() == self.color)
    }
}

impl<D, A, const OMEGA: bool> From<D> for Automaton<D, A, OMEGA>
where
    D: Congruence,
    A: Default,
{
    fn from(value: D) -> Self {
        let initial = value.initial();
        Self::from_parts(value, initial, A::default())
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn mealy_color_or_below() {
        let mm = MooreMachine::builder()
            .with_state_colors([0, 1, 1, 0])
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 2),
                (1, 'a', 2),
                (1, 'b', 2),
                (2, 'a', 3),
                (2, 'b', 3),
                (3, 'a', 3),
                (3, 'b', 3),
            ])
            .into_moore(0);

        let dfas = mm.decompose_dfa();
        let dfa1 = &dfas[1];
        let dfa0 = &dfas[0];

        println!("{:?}", dfa0);
        assert!(dfa1.accepts(""));
        assert!(dfa1.accepts("b"));
        assert!(!dfa0.accepts("b"));
        assert!(dfa0.accepts("ba"));
    }

    #[test]
    fn dbas() {
        let dba = DBA::builder()
            .with_edges([
                (0, 'a', true, 1),
                (0, 'b', false, 0),
                (1, 'a', true, 1),
                (1, 'b', false, 0),
            ])
            .into_dba(0);
        assert!(dba.accepts(ReducedOmegaWord::periodic("abb")));
        assert!(!dba.accepts(ReducedOmegaWord::periodic("b")));
        assert!(dba.accepts(upw!("a")));
        assert!(!dba.accepts(upw!("b")));

        assert!(!dba.is_empty());
        println!("{:?}", dba.give_word());

        println!("{:?}", &dba);
    }

    #[test]
    fn dfas_and_boolean_operations() {
        let dfa = DFA::builder()
            .with_state_colors([true, false])
            .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 0)])
            .into_dfa(0);

        assert!(!dfa.is_empty_language());
        assert_eq!(dfa.give_word(), Some(vec![]));

        let _dfb = dfa.clone();

        assert!(dfa.accepts("ababab"));
        assert!(!dfa.accepts("a"));

        let notdfa = dfa.as_ref().negation().into_dfa();
        assert!(!notdfa.accepts("ababab"));
        assert!(notdfa.accepts("a"));

        let intersection = dfa.as_ref().intersection(&notdfa).into_dfa();
        assert!(!intersection.accepts("ababab"));
        assert!(!intersection.accepts("a"));

        let union = dfa.as_ref().union(&notdfa).into_dfa();
        assert!(union.accepts("ababab"));
        assert!(union.accepts("a"));
    }
}
