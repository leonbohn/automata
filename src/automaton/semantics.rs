use crate::TransitionSystem;
use crate::automaton::{MealySemantics, MooreSemantics};
use crate::ts::run::{Observer, ReachedEdgeColor, ReachedStateColor};
use crate::ts::{Deterministic, EdgeColor, StateColor, StateIndex, SymbolOf};
use crate::word::{FiniteWord, OmegaWord};

/// This is the base trait for different types of semantics that are used by the
/// [`crate::Automaton`] struct for determining the output of a finite or infinite
/// input. This can either be some arbitrary output in the case of a Moore or
/// Mealy machine. Or it could be boolean indicating whether the input is
/// accepted or not in case of an acceptor like a DFA.
///
/// The second parameter `W` is the type of word that is read. Whether an automaton reads
/// finite or infinite words is determined by which `W` its [`Semantics`] are implemented
/// for.
///
/// # Deterministic semantics
/// Most semantics require a [`Deterministic`] transition system and look at the single run of
/// the word, collecting information about it with an [`Observer`] (see
/// [`crate::ts::run::Run::observe`]):
///
/// - [`MooreSemantics`] output the color of the state that a finite word reaches, the
///   [`crate::automaton::ReachabilityCondition`] of a [`crate::automaton::DFA`] does the same for
///   `bool` state colors, and [`MealySemantics`] output the color of the last edge.
/// - For infinite words, the [`crate::automaton::BuchiCondition`] accepts if an edge labeled with
///   `true` is taken infinitely often, the [`crate::automaton::MinEvenParityCondition`] of a
///   [`crate::automaton::DPA`] if the least priority that is seen infinitely often is even.
///
/// # Nondeterministic semantics
/// The branching of an automaton is part of the type of its semantics: wrapping an acceptance
/// condition in [`crate::automaton::Existential`] accepts a word if *some* run on it satisfies
/// the condition, which works on any [`TransitionSystem`]. This is how
/// [`crate::automaton::NFA`], [`crate::automaton::NBA`] and the other nondeterministic automata
/// are defined.
pub trait Semantics<T: TransitionSystem, W> {
    /// The type of output that this semantic produces.
    type Output;
    /// Returns the output for `word` read in `ts` from `initial`, or `None` if it is not
    /// defined, for example because the run of a deterministic system leaves the system.
    fn output(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<Self::Output>;
}

/// Runs a finite word and returns what the observer `O` has collected.
pub(crate) fn observe_finite<T, W, O>(ts: &T, initial: StateIndex<T>, word: W) -> Option<O::Current>
where
    T: Deterministic,
    W: FiniteWord<Symbol = SymbolOf<T>>,
    O: Observer<T>,
{
    ts.run_from(initial, word).observe::<O>()
}

/// Runs an omega word and returns what the observer `O` has collected.
pub(crate) fn observe_omega<T, W, O>(ts: &T, initial: StateIndex<T>, word: W) -> Option<O::Current>
where
    T: Deterministic,
    W: OmegaWord<Symbol = SymbolOf<T>>,
    O: Observer<T>,
{
    ts.run_from(initial, word).observe::<O>()
}

impl<T: Deterministic, W: FiniteWord<Symbol = SymbolOf<T>>> Semantics<T, W> for MealySemantics {
    type Output = EdgeColor<T>;
    fn output(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<Self::Output> {
        // the empty word takes no edge and has no output
        observe_finite::<T, W, ReachedEdgeColor<T>>(ts, initial, word).flatten()
    }
}

impl<T: Deterministic, W: FiniteWord<Symbol = SymbolOf<T>>> Semantics<T, W> for MooreSemantics {
    type Output = StateColor<T>;
    fn output(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<Self::Output> {
        observe_finite::<T, W, ReachedStateColor<T>>(ts, initial, word)
    }
}
