pub(crate) mod partition_refinement;

use crate::Color;
use crate::DTS;
use crate::Void;
use crate::automaton::{DFA, MealyMachine, MooreMachine};
use crate::representation::IntoTs;
use crate::ts::{Deterministic, EdgeColor, StateColor};

impl<D> MooreMachine<D>
where
    D: Deterministic,
    StateColor<D>: Color + Eq + std::hash::Hash,
{
    /// Returns the unique minimal moore machine that is bisimilar to `self`. This means
    /// for every finite word, the output of `self` and the output of the returned moore
    /// machine is the same. This is done using the Hopcroft and Moore algorithms for
    /// minimizing deterministic finite automata.
    pub fn minimize(&self) -> MooreMachine<DTS<D::Alphabet, D::StateColor, Void>> {
        partition_refinement::moore_partition_refinement(self)
    }
}

impl<D> MealyMachine<D>
where
    D: Deterministic,
    EdgeColor<D>: Color + Eq + std::hash::Hash,
{
    /// Minimizes `self` using Hopcroft's partition refinement algorithm.
    pub fn minimize(&self) -> partition_refinement::MinimizedMealy<D> {
        partition_refinement::mealy_partition_refinement(self)
    }
}

impl<D> DFA<D>
where
    D: Deterministic<StateColor = bool>,
{
    /// Minimizes `self` using Hopcroft's partition refinement algorithm.
    pub fn minimize(self) -> DFA<DTS<D::Alphabet, bool, Void>> {
        let min = partition_refinement::moore_partition_refinement(self);
        min.into_dfa()
    }
}
