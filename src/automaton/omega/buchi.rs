use crate::States;
use crate::alphabet::CharAlphabet;
use crate::automaton::semantics::observe_omega;
use crate::automaton::{CycleCondition, DPA, Existential, HistoryDeterministic, Semantics};
use crate::representation::IntoTransitions;
use crate::ts::{Deterministic, StateIndex, SymbolOf};
use crate::word::OmegaWord;
use crate::{DTS, TransitionSystem, automaton::Automaton, ts::run};
use crate::{Int, Void};
use crate::{NTS, math};

/// Defines the [`Semantics`] of a deterministic Büchi automaton (DBA),
/// which is an acceptor of infinite words. It considers the set of
/// transitions which is taken infinitely often. If one of those is
/// colored with `true`, then the automaton accepts, while if all of the
/// transitions that are taken infinitely often are colored with `false`,
/// the automaton rejects.
///
/// This type will rarely be used on its own, for the automaton that makes
/// use of it, see [`DBA`].
#[derive(Debug, Default, Clone, Eq, PartialEq, Hash, Copy)]
pub struct BuchiCondition;

impl<T, W> Semantics<T, W> for BuchiCondition
where
    T: Deterministic<EdgeColor = bool>,
    W: OmegaWord<Symbol = SymbolOf<T>>,
{
    type Output = bool;
    fn output(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<bool> {
        observe_omega::<T, W, run::GreatestEdgeColor<T>>(ts, initial, word)
    }
}

impl CycleCondition for BuchiCondition {
    type Color = bool;
    fn satisfied_by(&self, colors: &math::FxIndexSet<bool>) -> bool {
        colors.contains(&true)
    }
    fn avoid(&self, _: &math::FxIndexSet<bool>) -> Vec<Vec<bool>> {
        // a component without an accepting edge has no accepting cycle
        Vec::new()
    }
}

/// A nondeterministic Büchi automaton (NBA): it accepts an infinite word if *some* run on it takes
/// an edge colored with `true` infinitely often, see [`Existential`]. Unlike a [`DBA`], it can
/// recognize every omega-regular language.
///
/// ```
/// use automata::prelude::*;
///
/// // eventually only `b`, which no DBA recognizes: guess when the last `a` has been read
/// let nba = Builder::without_state_colors()
///     .with_transitions([(0, 'a', false, 0), (0, 'b', false, 0), (0, 'b', true, 1), (1, 'b', true, 1)])
///     .into_nba(0);
/// assert!(nba.accepts(upw!("ab", "b")));
/// assert!(!nba.accepts(upw!("ab")));
/// ```
pub type NBA<T = NTS<CharAlphabet, Void, bool>> = Automaton<T, Existential<BuchiCondition>>;

/// A history-deterministic Büchi automaton, an [`NBA`] whose nondeterminism can be resolved on
/// the fly, see [`HistoryDeterministic`].
pub type HDBA<T = NTS<CharAlphabet, Void, bool>> =
    Automaton<T, HistoryDeterministic<BuchiCondition>>;

/// A deterministic Büchi automaton (DBA) is a deterministic automaton with Büchi acceptance condition.
/// It accepts a word if it has a successful infinite run that takes an accepting
/// transition (i.e. one that is labeled with `true`) infinitely often.
///
/// In a certain sense, it is a special case of a deterministic parity automaton [`super::DPA`] with
/// min even and priorities 0 and 1.
pub type DBA<T = DTS<CharAlphabet, Void, bool>> = Automaton<T, BuchiCondition>;

impl<C> DBA<C>
where
    C: Deterministic<EdgeColor = bool> + States,
{
    /// Performs a streamlining operation akin to [`super::DPA::streamlined`].
    pub fn streamlined(&self) -> DBA<DTS<C::Alphabet, Void, bool>>
    where
        C: IntoTransitions<Initial = ()> + Clone,
    {
        let dpa: DPA<DTS<C::Alphabet, Void, Int>> = self
            .clone()
            .map_edge_colors(|c| if c { 0 } else { 1 })
            .erase_state_colors()
            .collect();
        dpa.streamlined()
            .map_edge_colors(|c| {
                debug_assert!(c == 0 || c == 1, "streamlining keeps the two priorities");
                c % 2 == 0
            })
            .collect()
    }
}
