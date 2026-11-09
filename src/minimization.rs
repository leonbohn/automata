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
//!
//! // unreachable states are removed
//! let unreachable = Builder::default()
//!     .with_state_colors([true, false])
//!     .with_transitions([(0, 'a', 0), (0, 'b', 0), (1, 'a', 0), (1, 'b', 1)])
//!     .into_dfa(0);
//! assert_eq!(Minimize::on(&unreachable).run().state_count(), 1);
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
/// States that are not reachable from the initial state are removed. The states of the result are
/// numbered in the order in which a breadth-first search from the initial state discovers them, so
/// the initial state is state `0`. For a [`MealyMachine`], the state colors of the result are the
/// colors of the (reachable) states that have been merged.
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
    /// Computes the minimal [`MooreMachine`] with the same output on every finite word. Unreachable
    /// states are removed.
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
    /// Unreachable states are removed.
    pub fn run(self) -> partition_refinement::MinimizedMealy<D> {
        partition_refinement::mealy_partition_refinement(self.0)
    }
}

impl<D> Minimize<'_, DFA<D>>
where
    D: Deterministic<StateColor = bool> + States,
{
    /// Computes the minimal [`DFA`] that accepts the same language. Unreachable states are removed.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automaton::Equivalence;
    use crate::ts::{Builder, Pointed, TransitionSystem, q};

    #[test]
    fn unreachable_states_are_removed_and_the_initial_state_is_first() {
        // state 0 and 3 are unreachable, 2 is initial; 1 and 2 have the same behavior
        let dfa = Builder::default()
            .with_state_colors([true, false, false, true])
            .with_transitions([
                (0, 'a', 1),
                (0, 'b', 0),
                (1, 'a', 2),
                (1, 'b', 1),
                (2, 'a', 1),
                (2, 'b', 2),
                (3, 'a', 3),
                (3, 'b', 3),
            ])
            .into_dfa(2);
        let minimal = dfa.clone().minimize();
        assert_eq!(minimal.state_count(), 1);
        assert_eq!(minimal.initial(), q(0));
        assert!(Equivalence::of(&dfa).and(&minimal).holds());
    }

    #[test]
    fn minimal_machines_only_have_reachable_states() {
        let ts = Builder::default()
            .with_state_colors([0u8, 1, 1, 0])
            .with_transitions([
                (0, 'a', 1),
                (0, 'b', 3),
                (1, 'a', 2),
                (1, 'b', 3),
                (2, 'a', 1),
                (2, 'b', 3),
                (3, 'a', 3),
                (3, 'b', 3),
            ]);
        let moore = ts.into_moore(1);
        let minimal = moore.minimize();
        // 1 and 2 are merged, 0 is not reachable
        assert_eq!(minimal.state_count(), 2);
        assert_eq!(minimal.initial(), q(0));
        assert_eq!(minimal.reachable_state_indices().count(), 2);

        let mealy = Builder::without_state_colors()
            .with_transitions([
                (0, 'a', 0u8, 1),
                (0, 'b', 1, 0),
                (1, 'a', 0, 1),
                (1, 'b', 1, 1),
            ])
            .into_mealy(1);
        let minimal = mealy.minimize();
        assert_eq!(minimal.state_count(), 1);
        assert_eq!(minimal.initial(), q(0));
    }
}
