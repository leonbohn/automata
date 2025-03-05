pub(crate) mod partition_refinement;

use crate::automaton::{
    DFA, IntoDFA, IntoMealyMachine, IntoMooreMachine, MealyMachine, MooreMachine,
};
use crate::core::Color;
use crate::representation::IntoTs;
use crate::ts::{Deterministic, EdgeColor, StateColor};

impl<D> IntoMooreMachine<D>
where
    D: Deterministic,
    StateColor<D>: Color,
{
    /// Returns the unique minimal moore machine that is bisimilar to `self`. This means
    /// for every finite word, the output of `self` and the output of the returned moore
    /// machine is the same. This is done using the Hopcroft and Moore algorithms for
    /// minimizing deterministic finite automata.
    pub fn minimize(&self) -> MooreMachine<D::Alphabet, D::StateColor> {
        partition_refinement::moore_partition_refinement(self)
    }
}

impl<D> IntoMealyMachine<D>
where
    D: Deterministic,
    EdgeColor<D>: Color,
{
    /// Minimizes `self` using Hopcroft's partition refinement algorithm.
    pub fn minimize(&self) -> MealyMachine<D::Alphabet, Vec<StateColor<D>>, D::EdgeColor> {
        partition_refinement::mealy_partition_refinement(self)
    }
}

impl<D> IntoDFA<D>
where
    D: Deterministic<StateColor = bool>,
{
    /// Minimizes `self` using Hopcroft's partition refinement algorithm.
    pub fn minimize(self) -> DFA<D::Alphabet> {
        let min = partition_refinement::moore_partition_refinement(self);
        min.into_dfa()
    }
}
