//! Minimization of deterministic machines, stated as the problem [`Minimize`].
//!
//! ```
//! use automata::minimization::Minimize;
//! use automata::States;
//! use automata::ts::Builder;
//!
//! let dfa = Builder::default()
//!     .with_state_colors([false, true, true])
//!     .with_transitions([(0, 'a', 1), (0, 'b', 2), (1, 'a', 1), (1, 'b', 1), (2, 'a', 2), (2, 'b', 2)])
//!     .into_dfa(0);
//! assert_eq!(Minimize::on(&dfa).run().state_count(), 2);
//! ```

pub(crate) mod partition_refinement;

use crate::Color;
use crate::DTS;
use crate::States;
use crate::Void;
use crate::automaton::{DFA, MealyMachine, MooreMachine};
use crate::ts::{Deterministic, EdgeColor, StateColor};

/// The problem of minimizing a deterministic machine: [`Minimize::on`] states it for a
/// [`DFA`], [`MooreMachine`] or [`MealyMachine`] and [`run`](Minimize::run) returns the unique
/// minimal machine that is bisimilar to it. The result is built directly from the partition
/// computed by Hopcroft's algorithm.
///
/// For a [`MealyMachine`], the state colors of the result are the colors of the states that have
/// been merged. States that are not reachable are minimized as well and are kept.
#[derive(Debug, Clone, Copy)]
pub struct Minimize<'a, M>(&'a M);

impl<'a, M> Minimize<'a, M> {
    /// States the problem for the given machine.
    pub fn on(machine: &'a M) -> Self {
        Self(machine)
    }
}

impl<D> Minimize<'_, MooreMachine<D>>
where
    D: Deterministic + States,
    StateColor<D>: Color + Eq + std::hash::Hash,
{
    /// Computes the minimal [`MooreMachine`] with the same output on every finite word.
    pub fn run(self) -> MooreMachine<DTS<D::Alphabet, D::StateColor, Void>> {
        partition_refinement::moore_partition_refinement(self.0)
    }
}

impl<D> Minimize<'_, MealyMachine<D>>
where
    D: Deterministic + States,
    EdgeColor<D>: Color + Eq + std::hash::Hash,
{
    /// Computes the minimal [`MealyMachine`] with the same output on every non-empty finite word.
    pub fn run(self) -> partition_refinement::MinimizedMealy<D> {
        partition_refinement::mealy_partition_refinement(self.0)
    }
}

impl<D> Minimize<'_, DFA<D>>
where
    D: Deterministic<StateColor = bool> + States,
{
    /// Computes the minimal [`DFA`] that accepts the same language.
    pub fn run(self) -> DFA<DTS<D::Alphabet, bool, Void>> {
        let (ts, initial, _) =
            partition_refinement::moore_partition_refinement(self.0).into_parts();
        DFA::from_parts(ts, initial)
    }
}

impl<D> MooreMachine<D>
where
    D: Deterministic + States,
    StateColor<D>: Color + Eq + std::hash::Hash,
{
    /// Returns the unique minimal moore machine that is bisimilar to `self`, see [`Minimize`].
    pub fn minimize(&self) -> MooreMachine<DTS<D::Alphabet, D::StateColor, Void>> {
        Minimize::on(self).run()
    }
}

impl<D> MealyMachine<D>
where
    D: Deterministic + States,
    EdgeColor<D>: Color + Eq + std::hash::Hash,
{
    /// Minimizes `self` using Hopcroft's partition refinement algorithm, see [`Minimize`].
    pub fn minimize(&self) -> partition_refinement::MinimizedMealy<D> {
        Minimize::on(self).run()
    }
}

impl<D> DFA<D>
where
    D: Deterministic<StateColor = bool> + States,
{
    /// Minimizes `self` using Hopcroft's partition refinement algorithm, see [`Minimize`].
    pub fn minimize(self) -> DFA<DTS<D::Alphabet, bool, Void>> {
        Minimize::on(&self).run()
    }
}
