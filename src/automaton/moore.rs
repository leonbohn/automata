use itertools::Itertools;
use std::fmt::Debug;

use crate::core::{Color, Int, Lattice, Void, alphabet::CharAlphabet, word::FiniteWord};

use super::{DFA, FiniteWordAutomaton, MealyMachine};
use crate::representation::{CollectTs, IntoTs};
use crate::ts::operations::{Product, ProductIndex};
use crate::ts::{Deterministic, EdgeColor, StateColor, SymbolOf};
use crate::{Congruence, DTS, Pointed, TransitionSystem};

/// Represents the semantics of a Moore machine, it produces the color of the
/// state that is reached during a run on a word. If the input is empty, it
/// produces the color of the initial state.
#[derive(Debug, Clone)]
pub struct MooreSemantics<Q>(std::marker::PhantomData<Q>);

pub trait MooreLike: TransitionSystem<StateColor: Lattice> + Deterministic + Pointed {}
impl<T: TransitionSystem<StateColor: Lattice> + Deterministic + Pointed> MooreLike for T {}

/// A Moore machine is a transition system where each state has an output. Thus, the output
/// of running a Moore machine on a word produces a sequence of outputs, one for each state
/// that is visited. For a word of length `n`, there are `n+1` outputs, note in particular
/// that the empty word produce an output, which is in contrast to [`MealyMachine`]s, where
/// the empty word produces no output.
///
/// Usually, we are interested in the output of the last state that is reached during a run
/// on a word. In case of a deterministic Moore machine, this is the only output that is
/// produced. A [`crate::automaton::DFA`] is then a Moore machine, where the colors are `bool`. A word reaches
/// a state and the corresponding `bool` is emitted, where `true` corresponds to an accepted
/// input, whereas `false` represents a rejected input. For infinite runs, we usually
/// consider the colors that are produced infinitely often and base acceptance around them. It
/// is, however, prefered to use a [`MealyMachine`] for this purpose, as for infinite inputs
/// switching to transition-based acceptance is preferable.
pub type MooreMachine<A = CharAlphabet, Q = Int, C = Void, D = DTS<A, Q, C>> =
    FiniteWordAutomaton<A, MooreSemantics<Q>, Q, C, true, D>;

/// Helper type that takes a pointed transition system and returns the corresponding
/// [`MooreMachine`], which the ts can be converted into using [`Into::into`].
/// For concrete automaton types such as [`crate::automaton::DFA`], the [`crate::automaton::IntoDFA`] type can be used to
/// obtain the type of a [`DFA`] for the given ts.
pub type IntoMooreMachine<D> =
    MooreMachine<<D as TransitionSystem>::Alphabet, StateColor<D>, EdgeColor<D>, D>;

impl<M> IntoMooreMachine<M>
where
    M: IntoTs<EdgeColor: Color> + Deterministic,
{
    /// Decomposes `self` into a sequence of DFAs, where the i-th DFA accepts all words which
    /// produce a color less than or equal to i.
    pub fn decompose_dfa(&self) -> Vec<DFA<M::Alphabet>>
    where
        StateColor<Self>: Ord,
    {
        self.color_range()
            .into_iter()
            .sorted()
            .map(|i| self.color_or_below_dfa(i))
            .collect()
    }

    /// Builds a DFA that accepts all words which emit a color less than or equal to `color`.
    pub fn color_or_below_dfa(&self, color: M::StateColor) -> DFA<M::Alphabet>
    where
        StateColor<Self>: Ord,
    {
        self.map_state_colors(|o| o <= color)
            .erase_edge_colors()
            .with_initial(self.initial)
            .collect_dfa()
            .minimize()
    }

    /// Pushes the state colors onto the outgoing edges of `self` and collects the resulting
    /// transition system into a new [`MealyMachine`].
    pub fn push_colors_to_outgoing_edges(
        &self,
    ) -> MealyMachine<M::Alphabet, M::StateColor, M::StateColor>
    where
        M::StateColor: Clone,
    {
        self.map_edge_colors_full(|p, _a, _c, _q| {
            self.state_color(p)
                .expect("We know it is reachable and it must be colored")
                .clone()
        })
        .with_initial(self.initial)
        .collect_mealy()
    }

    /// Runs the given `input` word in self. If the run is successful, the color of the state that it reaches
    /// is emitted (wrapped in a `Some`). For unsuccessful runs, `None` is returned.
    pub fn map<W: FiniteWord<Symbol = SymbolOf<Self>>>(&self, input: W) -> Option<M::StateColor> {
        self.reached_state_color_from(self.initial, input)
    }

    /// Obtains a vec containing the possible colors emitted by `self` (without duplicates).
    pub fn color_range(&self) -> Vec<M::StateColor>
    where
        StateColor<Self>: Color,
    {
        self.reachable_state_indices_from(self.initial)
            .map(|o| {
                self.state_color(o)
                    .expect("We know it is reachable and it must be colored")
            })
            .unique()
            .collect()
    }

    /// Returns true if `self` is bisimilar to `other`, i.e. if the two moore machines
    /// produce the same output for each finite word. This is done by checking whether
    /// [`Self::witness_non_bisimilarity`] returns `None`.
    pub fn bisimilar<N>(&self, other: N) -> bool
    where
        N: Congruence<Alphabet = M::Alphabet, StateColor = M::StateColor>,
        StateColor<Self>: Color,
    {
        self.witness_non_bisimilarity(other).is_none()
    }

    /// Returns a witness for the non-bisimilarity of `self` and `other`, i.e. a finite word
    /// that produces different outputs in the two moore machines. If the two machines are
    /// bisimilar, `None` is returned.
    pub fn witness_non_bisimilarity<N>(&self, other: N) -> Option<Vec<SymbolOf<Self>>>
    where
        N: Congruence<Alphabet = M::Alphabet, StateColor = M::StateColor>,
        StateColor<Self>: Color,
    {
        let other_initial = other.initial();
        let prod = self.ts_product(other);
        for mr in prod.minimal_representatives_iter_from(ProductIndex(self.initial, other_initial))
        {
            let (c, d) = prod.state_color(mr.state_index()).unwrap();
            if c != d {
                return Some(mr.decompose().0);
            }
        }
        None
    }
}

impl<Q> Default for MooreSemantics<Q> {
    fn default() -> Self {
        Self(std::marker::PhantomData)
    }
}
