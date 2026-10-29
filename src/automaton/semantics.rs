use crate::TransitionSystem;
use crate::automaton::{MealySemantics, MooreSemantics};
use crate::ts::run::{InfiniteObserver, Observer, ReachedEdgeColor, ReachedStateColor};
use crate::ts::{Deterministic, EdgeColor, StateColor, StateIndex, SymbolOf};
use crate::word::{FiniteWord, OmegaWord};

/// This is the base trait for different types of semantics that are used by the
/// [`crate::Automaton`] struct for determining the output of a finite or infinite
/// run. This can either be some arbitrary output in the case of a Moore or
/// Mealy machine. Or it could be boolean indicating whether the input is
/// accepted or not in case of an acceptor like a DFA.
///
/// The second parameter `W` is the type of word that is read. Whether an automaton reads
/// finite or infinite words is determined by which `W` its [`Semantics`] are implemented
/// for. The purpose of a semantic is to determine what to do with the run that is
/// induced by an input on some transition system.
///
/// # Finite inputs
/// For a finite input such as a [`crate::word::FiniteWord`] we use [`Semantics`],
/// which defines an `Output` type and provides the [`Semantics::evaluate`] method.
/// It takes the [`crate::ts::run::Run`] that is the result of running the finite
/// input in some transition system and turns it into the desired output.
///
/// Examples of this semantic are for example the [`MooreSemantics`], which
/// for a finite word `w` simply produce the color of the state that is
/// reached when running `w` in the transition system from the initial state.
/// This is similar to the [`crate::automaton::ReachabilityCondition`], which additionaly demand that
/// the state colors are `bool`.
/// Further, there is also the [`MealySemantics`], which outputs the last
/// transition that is taken when reading `w`.
///
/// # Infinite inputs
/// For an infinite input like an [`crate::word::OmegaWord`], we also need to define an
/// `Output` type. This is now computed in the [`Semantics::evaluate`] method on
/// the [`Semantics`] trait. It does this based on a [`crate::ts::run::Run`].
///
/// Examples include the [`crate::automaton::BuchiCondition`], which may be applied to `bool`
/// edge-colored transition systems. It outputs `true` if any edge labeled
/// with `true` is visited infinitely often and `false` otherwise.
/// This can actually be viewed as an instantiation of the [`crate::automaton::MinEvenParityCondition`]
/// semantics that a [`crate::automaton::DPA`] uses, which outputs the least priority/color
/// among those that are labels of edges taken infinitely often.
pub trait Semantics<T: TransitionSystem, W> {
    /// The type of output that this semantic produces.
    type Output;
    /// The observer whose output is used for computing the output.
    type Observer: Observer<T>;

    /// Runs `word` in `ts` starting from `initial` and returns what the
    /// [`Self::Observer`] has collected. This is `None` if the run is not defined, i.e.
    /// if it leaves the transition system. Implementations for finite words use
    /// [`Deterministic::finite_run_from`], those for omega words use
    /// [`Deterministic::omega_run_from`].
    fn observe(
        &self,
        ts: &T,
        initial: StateIndex<T>,
        word: W,
    ) -> Option<<Self::Observer as Observer<T>>::Current>;

    /// Compute the output for the given observation of a run.
    fn evaluate(&self, observed: <Self::Observer as Observer<T>>::Current) -> Self::Output;
}

/// Runs a finite word and returns what the observer `O` has collected.
pub(crate) fn observe_finite<T, W, O>(ts: &T, initial: StateIndex<T>, word: W) -> Option<O::Current>
where
    T: Deterministic,
    W: FiniteWord<Symbol = SymbolOf<T>>,
    O: Observer<T>,
{
    ts.finite_run_from::<W, O>(initial, word).into_output()
}

/// Runs an omega word and returns what the observer `O` has collected.
pub(crate) fn observe_omega<T, W, O>(ts: &T, initial: StateIndex<T>, word: W) -> Option<O::Current>
where
    T: Deterministic,
    W: OmegaWord<Symbol = SymbolOf<T>>,
    O: InfiniteObserver<T>,
{
    ts.omega_run_from::<W, O>(initial, word).into_output()
}

impl<T: Deterministic, W: FiniteWord<Symbol = SymbolOf<T>>> Semantics<T, W> for MealySemantics {
    type Output = EdgeColor<T>;
    type Observer = ReachedEdgeColor<T>;
    fn observe(
        &self,
        ts: &T,
        initial: StateIndex<T>,
        word: W,
    ) -> Option<<Self::Observer as Observer<T>>::Current> {
        observe_finite::<T, W, Self::Observer>(ts, initial, word)
    }
    fn evaluate(&self, observed: <Self::Observer as Observer<T>>::Current) -> Self::Output {
        observed
    }
}

impl<T: Deterministic, W: FiniteWord<Symbol = SymbolOf<T>>> Semantics<T, W> for MooreSemantics {
    type Output = StateColor<T>;
    type Observer = ReachedStateColor<T>;
    fn observe(
        &self,
        ts: &T,
        initial: StateIndex<T>,
        word: W,
    ) -> Option<<Self::Observer as Observer<T>>::Current> {
        observe_finite::<T, W, Self::Observer>(ts, initial, word)
    }
    fn evaluate(&self, observed: <Self::Observer as Observer<T>>::Current) -> Self::Output {
        observed
    }
}
