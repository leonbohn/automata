use crate::prelude::*;

mod acceptance_type;
pub use acceptance_type::OmegaAcceptanceType;

#[macro_use]
mod moore;
pub use moore::{IntoMooreMachine, MooreLike, MooreMachine};

#[macro_use]
mod mealy;
pub use mealy::{IntoMealyMachine, MealyLike, MealyMachine};

mod dfa;
pub use dfa::{DFALike, IntoDFA, DFA};

mod dpa;
pub use dpa::{DPALike, IntoDPA, MinEven, DPA};

mod dba;
pub use dba::{DBALike, IntoDBA, DBA};

#[allow(missing_docs)]
mod omega;
pub use omega::{
    AcceptanceMask, DeterministicOmegaAutomaton, OmegaAcceptanceCondition, OmegaAutomaton,
};

mod with_initial;
pub use with_initial::Initialized;

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
/// must implement the `FiniteSemantics` or `OmegaSemantics` trait, depending on
/// the value of `OMEGA` (in the former case `OMEGA` should be false, and in the
/// latter case `OMEGA` should be true).
#[derive(Clone, Eq, PartialEq, Copy)]
pub struct Automaton<D, A, const OMEGA: bool = false> {
    ts: D,
    acceptance: A,
}

impl<D, A, const OMEGA: bool> Automaton<D, A, OMEGA> {
    /// Creates a new automaton from the given transition system and acceptance condition.
    pub fn from_parts(ts: D, acceptance: A) -> Self {
        Self { ts, acceptance }
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

impl<D, A, const OMEGA: bool> AsRef<Automaton<D, A, OMEGA>> for Automaton<D, A, OMEGA> {
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

impl<D: Pointed, A, const OMEGA: bool> Pointed for Automaton<D, A, OMEGA> {
    fn initial(&self) -> Self::StateIndex {
        self.ts.initial()
    }
}

impl<D: Sproutable, A: Default, const OMEGA: bool> Sproutable for Automaton<D, A, OMEGA> {
    fn new_for_alphabet(alphabet: Self::Alphabet) -> Self {
        Automaton::from_parts(D::new_for_alphabet(alphabet), Default::default())
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

impl<T, A, const OMEGA: bool> std::fmt::Debug for Automaton<T, A, OMEGA>
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

/// This trait is implemented by acceptance conditions for finite words.
pub trait FiniteSemantics<Q, C> {
    /// The type of output that this semantic produces.
    type Output;
    /// Compute the output for the given finite run.
    fn finite_semantic<R>(&self, run: R) -> Self::Output
    where
        R: FiniteRun<StateColor = Q, EdgeColor = C>;
}

/// This trait is implemented by acceptance conditions for omega words.
pub trait OmegaSemantics<Q, C> {
    /// The type of output that this semantic produces.
    type Output;
    /// Compute the output for the given omega run.
    fn omega_semantic<R>(&self, run: R) -> Self::Output
    where
        R: OmegaRun<StateColor = Q, EdgeColor = C>;
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

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn mealy_color_or_below() {
        let mut mm: MooreMachine<CharAlphabet, usize> =
            MooreMachine::new_for_alphabet(alphabet!(simple 'a', 'b'));
        let a = mm.add_state(0usize);
        let b = mm.add_state(1usize);
        let c = mm.add_state(1usize);
        let d = mm.add_state(0usize);
        mm.add_edge(a, 'a', b, Void);
        mm.add_edge(a, 'b', c, ());
        mm.add_edge(b, 'a', c, ());
        mm.add_edge(b, 'b', c, ());
        mm.add_edge(c, 'a', d, ());
        mm.add_edge(c, 'b', c, ());
        mm.add_edge(d, 'a', d, ());
        mm.add_edge(d, 'b', d, ());

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
        let mut dba = super::DBA::new_for_alphabet(CharAlphabet::from_iter(['a', 'b']));
        let q0 = dba.add_state(());
        let q1 = dba.add_state(Void);

        let _e0 = dba.add_edge(q0, 'a', q1, true);
        let _e1 = dba.add_edge(q0, 'b', q0, false);
        let _e2 = dba.add_edge(q1, 'a', q1, true);
        let _e3 = dba.add_edge(q1, 'b', q0, false);
        assert!(dba.accepts(ReducedOmegaWord::periodic("abb")));
        assert!(!dba.accepts(ReducedOmegaWord::periodic("b")));
        assert!(dba.accepts(upw!("a")));
        assert!(!dba.accepts(upw!("b")));

        assert!(!dba.dba_is_empty());
        println!("{:?}", dba.dba_give_word());

        println!("{:?}", &dba);
    }

    #[test]
    fn dfas_and_boolean_operations() {
        let mut dfa = super::DFA::new_for_alphabet(CharAlphabet::new(['a', 'b']));
        let s0 = dfa.add_state(true);
        let s1 = dfa.add_state(false);
        let _e0 = dfa.add_edge(s0, 'a', s1, Void);
        let _e1 = dfa.add_edge(s0, 'b', s0, Void);
        let _e2 = dfa.add_edge(s1, 'a', s1, Void);
        let _e3 = dfa.add_edge(s1, 'b', s0, Void);

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
