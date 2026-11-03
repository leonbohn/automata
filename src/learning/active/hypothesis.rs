use super::{Experiment, Experiments};
use crate::automaton::{MealyMachine, MooreMachine};
use crate::ts::{Deterministic, StateId, SymbolOf};
use crate::{Color, Void, alphabet::Alphabet, word::FiniteWord};
use crate::{DTS, Pointed, TransitionSystem};
use std::hash::Hash;

/// A hypothesis that L* can build: a Mealy or Moore machine whose `Output` is the output of the oracle.
///
/// The methods that look at the output of a word expect the hypothesis to be complete, as the
/// hypotheses that L* builds always are.
pub trait Hypothesis: TransitionSystem + Deterministic + Pointed {
    /// The type of the outputs that the hypothesis assigns to words.
    type Output: Color + Eq + Hash;

    /// Returns the output for `input` when starting in `source`.
    ///
    /// # Panics
    /// Panics if the hypothesis is not complete, i.e. if the run on `input` escapes.
    fn output_from<W: FiniteWord<Symbol = <Self::Alphabet as Alphabet>::Symbol>>(
        &self,
        input: W,
        source: Self::StateIndex,
    ) -> Self::Output;
    /// Returns the output for `input`.
    ///
    /// # Panics
    /// Panics if the hypothesis is not complete, i.e. if the run on `input` escapes.
    fn output<W: FiniteWord<Symbol = <Self::Alphabet as Alphabet>::Symbol>>(
        &self,
        input: W,
    ) -> Self::Output {
        self.output_from(input, self.initial())
    }

    /// Builds the hypothesis from the transition system that L* constructed and its initial state.
    fn from_transition_system(
        ts: DTS<Self::Alphabet, Self::StateColor, Self::EdgeColor>,
        initial: StateId,
    ) -> Self;
    /// Gives the color of the state that belongs to the representative `mr` with the given row of the table.
    fn give_state_color(
        mr: &[SymbolOf<Self>],
        experiments: &Experiments<Self>,
        row: &[Self::Output],
    ) -> Self::StateColor;

    /// Gives the color of the edge that reads `a` from the state of `source_mr` to the state of `target_mr`.
    ///
    /// # Panics
    /// May panic if the rows do not belong to the experiments, which cannot happen when called by L*.
    fn give_transition_color(
        source_mr: &[SymbolOf<Self>],
        a: SymbolOf<Self>,
        target_mr: &[SymbolOf<Self>],
        experiments: &Experiments<Self>,
        source_row: &[Self::Output],
        target_row: &[Self::Output],
    ) -> Self::EdgeColor;

    /// The experiments that the table must contain from the start.
    fn mandatory_experiments(
        alphabet: &Self::Alphabet,
    ) -> impl IntoIterator<Item = Experiment<SymbolOf<Self>>>;
}

impl<A: Alphabet, Q: Color + Eq + Hash> Hypothesis for MooreMachine<DTS<A, Q, Void>> {
    type Output = Q;

    fn output_from<W: FiniteWord<Symbol = <Self::Alphabet as Alphabet>::Symbol>>(
        &self,
        input: W,
        source: Self::StateIndex,
    ) -> Self::Output {
        self.run_from(source, input)
            .reached_state_color()
            .expect("Hypothesis must be complete")
    }
    fn from_transition_system(
        ts: DTS<Self::Alphabet, Self::StateColor, Self::EdgeColor>,
        initial: StateId,
    ) -> Self {
        Self::from_parts(ts, initial)
    }
    fn mandatory_experiments(
        _alphabet: &Self::Alphabet,
    ) -> impl IntoIterator<Item = Experiment<SymbolOf<Self>>> {
        [Experiment::empty()]
    }
    fn give_state_color(
        _mr: &[SymbolOf<Self>],
        experiments: &Experiments<Self>,
        row: &[Self::Output],
    ) -> Self::StateColor {
        debug_assert!(
            experiments
                .first()
                .expect("we need at least one experiment")
                .0
                .is_empty(),
            "first experiment should be empty word!"
        );
        row[0].clone()
    }
    fn give_transition_color(
        _source_mr: &[SymbolOf<Self>],
        _a: SymbolOf<Self>,
        _target_mr: &[SymbolOf<Self>],
        _experiments: &Experiments<Self>,
        source_row: &[Self::Output],
        _target_row: &[Self::Output],
    ) -> Self::EdgeColor {
        assert!(!source_row.is_empty(), "cannot have zero experiments");
        Void
    }
}

impl<A: Alphabet, C: Color + Eq + Hash> Hypothesis for MealyMachine<DTS<A, Void, C>> {
    type Output = C;

    fn output_from<W: FiniteWord<Symbol = <Self::Alphabet as Alphabet>::Symbol>>(
        &self,
        input: W,
        source: Self::StateIndex,
    ) -> Self::Output {
        self.run_from(source, input)
            .last_edge_color()
            .expect("Hypothesis must be complete")
    }
    fn from_transition_system(
        ts: DTS<Self::Alphabet, Self::StateColor, Self::EdgeColor>,
        initial: StateId,
    ) -> Self {
        Self::from_parts(ts, initial)
    }
    fn give_state_color(
        _mr: &[SymbolOf<Self>],
        _experiments: &Experiments<Self>,
        _row: &[Self::Output],
    ) -> Self::StateColor {
        Void
    }
    fn mandatory_experiments(
        alphabet: &Self::Alphabet,
    ) -> impl IntoIterator<Item = Experiment<SymbolOf<Self>>> {
        alphabet.universe().map(|a| Experiment(vec![a]))
    }
    fn give_transition_color(
        _source_mr: &[SymbolOf<Self>],
        a: SymbolOf<Self>,
        _target_mr: &[SymbolOf<Self>],
        experiments: &Experiments<Self>,
        source_row: &[Self::Output],
        _target_row: &[Self::Output],
    ) -> Self::EdgeColor {
        let Some(i) = experiments.iter().position(|b| b.is_letter(a)) else {
            panic!("could not find experiment for {a:?}");
        };
        assert!(source_row.len() > i);
        source_row[i].clone()
    }
}
