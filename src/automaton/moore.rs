use itertools::Itertools;
use std::fmt::Debug;

use crate::{Color, Int, Lattice, Void, alphabet::CharAlphabet, word::FiniteWord};

use super::{Automaton, DFA, MealyMachine};
use crate::representation::{CollectTs, IntoTs};
use crate::ts::operations::{Product, ProductIndex};
use crate::ts::{Deterministic, StateColor, SymbolOf};
use crate::{Congruence, DTS, Pointed, TransitionSystem};

/// Represents the semantics of a Moore machine, it produces the color of the
/// state that is reached during a run on a word. If the input is empty, it
/// produces the color of the initial state.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct MooreSemantics;

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
pub type MooreMachine<T = DTS<CharAlphabet, Int, Void>> = Automaton<T, MooreSemantics>;

impl<M> MooreMachine<M>
where
    M: IntoTs<EdgeColor: Color> + Deterministic,
{
    /// Decomposes `self` into a sequence of DFAs, where the i-th DFA accepts all words which
    /// produce a color less than or equal to i.
    pub fn decompose_dfa(&self) -> Vec<DFA<DTS<M::Alphabet, bool, Void>>>
    where
        StateColor<Self>: Ord + Eq + std::hash::Hash,
    {
        self.color_range()
            .into_iter()
            .sorted()
            .map(|i| self.color_or_below_dfa(i))
            .collect()
    }

    /// Builds a DFA that accepts all words which emit a color less than or equal to `color`.
    pub fn color_or_below_dfa(&self, color: M::StateColor) -> DFA<DTS<M::Alphabet, bool, Void>>
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
    ) -> MealyMachine<DTS<M::Alphabet, M::StateColor, M::StateColor>>
    where
        M::StateColor: Clone,
    {
        self.map_edge_colors_full(|p, _a, _c, _q| {
            self.state_color(p)
                .expect("We know it is reachable and it must be colored")
                .into_owned()
        })
        .with_initial(self.initial)
        .collect_mealy()
    }

    /// Runs the given `input` word in self. If the run is successful, the color of the state that it reaches
    /// is emitted (wrapped in a `Some`). For unsuccessful runs, `None` is returned.
    pub fn map<W: FiniteWord<Symbol = SymbolOf<Self>>>(&self, input: W) -> Option<M::StateColor> {
        self.run_from(self.initial, input).reached_state_color()
    }

    /// Obtains a vec containing the possible colors emitted by `self` (without duplicates).
    pub fn color_range(&self) -> Vec<M::StateColor>
    where
        StateColor<Self>: Color + Eq + std::hash::Hash,
    {
        self.reachable_state_indices_from(self.initial)
            .map(|o| {
                self.state_color(o)
                    .expect("We know it is reachable and it must be colored")
                    .into_owned()
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
        StateColor<Self>: Color + PartialEq,
    {
        self.witness_non_bisimilarity(other).is_none()
    }

    /// Returns a witness for the non-bisimilarity of `self` and `other`, i.e. a finite word
    /// that produces different outputs in the two moore machines. If the two machines are
    /// bisimilar, `None` is returned.
    pub fn witness_non_bisimilarity<N>(&self, other: N) -> Option<Vec<SymbolOf<Self>>>
    where
        N: Congruence<Alphabet = M::Alphabet, StateColor = M::StateColor>,
        StateColor<Self>: Color + PartialEq,
    {
        let other_initial = other.initial();
        let prod = self.ts_product(other);
        for mr in prod.minimal_representatives_iter_from(ProductIndex(self.initial, other_initial))
        {
            let colors = prod.state_color(mr.state_index()).unwrap();
            let (c, d) = &*colors;
            if c != d {
                return Some(mr.decompose().0);
            }
        }
        None
    }
}
