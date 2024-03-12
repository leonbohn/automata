#![allow(missing_docs)]
use itertools::Itertools;
use std::{fmt::Debug, hash::Hash, marker::PhantomData};

use crate::{prelude::*, Void};

use super::{Automaton, MooreLike};

/// Represents the semantics of a Mealy machine. Concretely, this type returns for
/// a finite run, the last transition color that is taken. It panics if the run has
/// no transitions at all.
#[derive(Debug, Clone, Default)]
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
    Automaton<Initialized<DTS<A, Void, C>>, MealySemantics<C>, false>;

/// Helper type that takes a pointed transition system and returns the corresponding
/// [`MealyMachine`].
pub type IntoMealyMachine<D> = Automaton<D, MealySemantics<EdgeColor<D>>, false>;

impl<Ts: Congruence> IntoMealyMachine<Ts>
where
    EdgeColor<Ts>: Color,
{
    pub fn restricted_inequivalence<
        O: MealyLike<Alphabet = Ts::Alphabet, EdgeColor = Ts::EdgeColor>,
    >(
        &self,
        other: &IntoMealyMachine<O>,
    ) -> Option<Vec<SymbolOf<Ts>>> {
        let prod = self.ts_product(other);
        for (mut rep, ProductIndex(l, r)) in prod.minimal_representatives() {
            'edges: for edge in self.edges_from(l).unwrap() {
                let Some(sym) = edge.expression().symbols().next() else {
                    continue 'edges;
                };
                let mut it = other.edges_from(r).unwrap();

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

    pub fn witness_inequivalence<
        O: MealyLike<Alphabet = Ts::Alphabet, EdgeColor = Ts::EdgeColor>,
    >(
        &self,
        other: &IntoMealyMachine<O>,
    ) -> Option<Vec<SymbolOf<Ts>>> {
        self.restricted_inequivalence(other)
            .or(other.restricted_inequivalence(self))
    }
}

/// Implemented by objects which can be viewed as a MealyMachine, i.e. a finite transition system
/// which has outputs of type usize on its edges.
pub trait MealyLike: Congruence {
    fn mealy_bisimilar<M>(&self, other: M) -> bool
    where
        M: Congruence,
        EdgeColor<M>: Color,
    {
        todo!()
    }

    /// Uses a reference to `self` for obtaining a [`MealyMachine`].
    fn as_mealy(&self) -> IntoMealyMachine<&Self>
    where
        EdgeColor<Self>: Color,
    {
        Automaton::from_parts(self, MealySemantics(PhantomData))
    }

    /// Self::EdgeColoronsumes `self`, returning a [`MealyMachine`] that uses the underlying transition system.
    fn into_mealy(self) -> IntoMealyMachine<Self>
    where
        EdgeColor<Self>: Color,
    {
        Automaton::from_parts(self, MealySemantics(PhantomData))
    }

    fn collect_mealy(self) -> MealyMachine<Self::Alphabet, Self::EdgeColor>
    where
        EdgeColor<Self>: Color,
    {
        self.erase_state_colors().collect_pointed().0.into_mealy()
    }

    /// Attempts to run the given finite word in `self`, returning the color of the last transition that
    /// is taken wrapped in `Some`. If no successful run on `input` is possible, the function returns `None`.
    fn try_mealy_map<W: FiniteWord<SymbolOf<Self>>>(&self, input: W) -> Option<Self::EdgeColor>
    where
        Self: Deterministic,
    {
        self.finite_run(input)
            .ok()
            .and_then(|r| r.last_transition_color().cloned())
    }

    /// Returns a vector over all colors that can be emitted.
    fn color_range(&self) -> impl Iterator<Item = Self::EdgeColor>
    where
        EdgeColor<Self>: Clone + Hash + Eq,
    {
        self.reachable_state_indices()
            .flat_map(|o| self.edges_from(o).unwrap().map(|e| IsEdge::color(&e)))
            .unique()
    }
}
impl<Ts: Congruence> MealyLike for Ts where EdgeColor<Ts>: Color {}

#[cfg(test)]
mod tests {
    use crate::{ts::NTS, TransitionSystem};

    use super::MealyLike;

    #[test]
    fn mealy_equivalence() {
        let mm1 = NTS::builder()
            .default_color(())
            .with_transitions([
                (0, 'a', 1, 0),
                (0, 'b', 0, 1),
                (1, 'a', 1, 0),
                (1, 'b', 0, 2),
                (2, 'a', 1, 0),
                (2, 'b', 0, 0),
            ])
            .deterministic()
            .with_initial(0)
            .into_mealy();
        let mm2 = NTS::builder()
            .default_color(())
            .with_transitions([
                (0, 'a', 1, 0),
                (0, 'b', 0, 1),
                (1, 'a', 1, 0),
                (1, 'b', 0, 2),
                (2, 'a', 1, 0),
                (2, 'b', 1, 0),
            ])
            .deterministic()
            .with_initial(0)
            .into_mealy();
        let mm3 = NTS::builder()
            .default_color(())
            .with_transitions([
                (0, 'a', 1, 0),
                (0, 'b', 0, 1),
                (1, 'a', 1, 0),
                (1, 'b', 0, 2),
                (2, 'a', 1, 0),
                (2, 'b', 0, 2),
            ])
            .deterministic()
            .with_initial(0)
            .into_mealy();

        assert_eq!(mm1.witness_inequivalence(&mm2), Some(vec!['b', 'b', 'b']))
    }
}
