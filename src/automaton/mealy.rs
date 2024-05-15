#![allow(missing_docs)]
use itertools::Itertools;
use std::{fmt::Debug, hash::Hash, marker::PhantomData};

use crate::prelude::*;

/// Represents the semantics of a Mealy machine. Concretely, this type returns for
/// a finite run, the last transition color that is taken. It panics if the run has
/// no transitions at all.
#[derive(Debug, Clone)]
pub struct MealySemantics<C>(PhantomData<C>);

/// A Mealy machine is a transition system where each transition has an output. Thus, the output
/// of running a Mealy machine on a word produces a sequence of outputs, one for each transition
/// that is taken. Note that since the empty word does not take any transitions, it does not
/// produce any output. For a word of length `n`, there are `n` outputs.
///
/// Usually, we are interested in the output of the last state that is reached during a run
/// on a word. In case of a deterministic Mealy machine, this is the only output that is
/// produced.
pub type MealyMachine<A = CharAlphabet, C = usize> =
    Automaton<DTS<A, Void, C>, MealySemantics<C>, false>;

/// Helper type that takes a pointed transition system and returns the corresponding
/// [`MealyMachine`].
pub type IntoMealyMachine<D> = Automaton<D, MealySemantics<EdgeColor<D>>, false>;

impl<C: Congruence> IntoMealyMachine<C>
where
    EdgeColor<C>: Color,
{
    /// Returns true if and only if both machines are bisimilar, meaning for all possible
    /// inputs, they will produce the same output.
    pub fn bisimilar<M>(&self, other: &IntoMealyMachine<M>) -> bool
    where
        M: Congruence<Alphabet = C::Alphabet, EdgeColor = C::EdgeColor>,
        EdgeColor<M>: Color,
    {
        self.witness_inequivalence(other).is_none()
    }

    /// Attempts to run the given finite word in `self`, returning the color of the last transition that
    /// is taken wrapped in `Some`. If no successful run on `input` is possible, the function returns `None`.
    pub fn map<W: FiniteWord<SymbolOf<Self>>>(&self, input: W) -> Option<EdgeColor<C>> {
        self.finite_run(input)
            .ok()
            .and_then(|r| r.last_transition_color().cloned())
    }

    /// Returns a vector over all colors that can be emitted.
    pub fn color_range(&self) -> impl Iterator<Item = C::EdgeColor> + '_
    where
        EdgeColor<Self>: Clone + Hash + Eq,
    {
        self.reachable_state_indices()
            .flat_map(|o| self.edges_from(o).unwrap().map(|e| IsEdge::color(&e)))
            .unique()
    }

    /// Checks for restricted inequivalence, meaning that the two machines produce
    /// different outputs. But this considers all outgoing edges in `self`, if any
    /// of those is missing, it will use this to produce a separating witness.
    /// However if the other machine has an edge that is not present in `self`, it
    /// will not be considered. This is why the operation needs to be run two times
    /// in [`Self::witness_inequivalence`].
    pub fn witness_restricted_inequivalence<
        O: Congruence<Alphabet = C::Alphabet, EdgeColor = C::EdgeColor>,
    >(
        &self,
        other: &IntoMealyMachine<O>,
    ) -> Option<Vec<SymbolOf<C>>> {
        let prod = self.ts_product(other);
        for (mut rep, ProductIndex(l, r)) in prod.minimal_representatives() {
            'edges: for edge in self.edges_from(l).unwrap() {
                let Some(sym) = edge.expression().symbols().next() else {
                    continue 'edges;
                };

                match other.transition(r, sym) {
                    Some(e) => {
                        if edge.color() != e.color() {
                            rep.push(sym);
                            return Some(rep);
                        }
                    }
                    None => {
                        rep.push(sym);
                        return Some(rep);
                    }
                }
            }
        }
        None
    }

    /// Attempts to construct a word that separates the two machines, meaning
    /// it produces different outputs whn run in both machines.
    /// If no such word exists, the function returns `None`.
    pub fn witness_inequivalence<
        O: Congruence<Alphabet = C::Alphabet, EdgeColor = C::EdgeColor>,
    >(
        &self,
        other: &IntoMealyMachine<O>,
    ) -> Option<Vec<SymbolOf<C>>> {
        self.witness_restricted_inequivalence(other)
            .or(other.witness_restricted_inequivalence(self))
    }
}

impl<Q> Default for MealySemantics<Q> {
    fn default() -> Self {
        Self(std::marker::PhantomData)
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn mealy_equivalence() {
        let mm1: MealyMachine = NTS::builder()
            .default_color(Void)
            .with_transitions([
                (0, 'a', 1, 0),
                (0, 'b', 0, 1),
                (1, 'a', 1, 0),
                (1, 'b', 0, 2),
                (2, 'a', 1, 0),
                (2, 'b', 0, 0),
            ])
            .into_dts()
            .with_initial(0)
            .into_mealy();
        let mm2: MealyMachine = NTS::builder()
            .default_color(Void)
            .with_transitions([
                (0, 'a', 1, 0),
                (0, 'b', 0, 1),
                (1, 'a', 1, 0),
                (1, 'b', 0, 2),
                (2, 'a', 1, 0),
                (2, 'b', 1, 0),
            ])
            .into_dts()
            .with_initial(0)
            .into_mealy();
        let _mm3: MealyMachine = NTS::builder()
            .default_color(Void)
            .with_transitions([
                (0, 'a', 1, 0),
                (0, 'b', 0, 1),
                (1, 'a', 1, 0),
                (1, 'b', 0, 2),
                (2, 'a', 1, 0),
                (2, 'b', 0, 2),
            ])
            .into_dts()
            .with_initial(0)
            .into_mealy();

        assert_eq!(mm1.witness_inequivalence(&mm2), Some(vec!['b', 'b', 'b']))
    }
}
