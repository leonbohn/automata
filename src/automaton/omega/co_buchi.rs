use crate::alphabet::CharAlphabet;
use crate::automaton::semantics::observe_omega;
use crate::automaton::{Automaton, CycleCondition, Existential, HistoryDeterministic, Semantics};
use crate::ts::{Deterministic, StateIndex, SymbolOf, run};
use crate::word::OmegaWord;
use crate::{DTS, NTS, Void, math};

/// The co-Büchi condition, the dual of the [`super::BuchiCondition`]: a run is accepting if it
/// takes edges colored with `true` only finitely often. See [`DCW`] and [`NCW`].
#[derive(Debug, Default, Clone, Eq, PartialEq, Hash, Copy)]
pub struct CoBuchiCondition;

impl<T, W> Semantics<T, W> for CoBuchiCondition
where
    T: Deterministic<EdgeColor = bool>,
    W: OmegaWord<Symbol = SymbolOf<T>>,
{
    type Output = bool;
    fn output(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<bool> {
        observe_omega::<T, W, run::GreatestEdgeColor<T>>(ts, initial, word).map(|seen| !seen)
    }
}

impl CycleCondition for CoBuchiCondition {
    type Color = bool;
    fn satisfied_by(&self, colors: &math::FxIndexSet<bool>) -> bool {
        !colors.contains(&true)
    }
    fn avoid(&self, _: &math::FxIndexSet<bool>) -> Vec<Vec<bool>> {
        vec![vec![true]]
    }
}

/// A deterministic co-Büchi automaton (DCW): it accepts an infinite word if its run takes edges
/// colored with `true` only finitely often.
///
/// ```
/// use automata::prelude::*;
///
/// // finitely many `a`
/// let dcw = Builder::without_state_colors()
///     .with_transitions([(0, 'a', true, 0), (0, 'b', false, 0)])
///     .into_dcw(0);
/// assert!(dcw.accepts(upw!("aa", "b")));
/// assert!(!dcw.accepts(upw!("ab")));
/// ```
pub type DCW<T = DTS<CharAlphabet, Void, bool>> = Automaton<T, CoBuchiCondition>;

/// A nondeterministic co-Büchi automaton (NCW): it accepts an infinite word if *some* run on it
/// takes edges colored with `true` only finitely often, see [`Existential`].
///
/// ```
/// use automata::prelude::*;
///
/// // eventually only `a` or eventually only `b`: guess when, then stay (waiting is `true`)
/// let ncw = Builder::without_state_colors()
///     .with_transitions([
///         (0, 'a', true, 0), (0, 'b', true, 0), (0, 'a', false, 1), (0, 'b', false, 2),
///         (1, 'a', false, 1), (1, 'b', true, 1), (2, 'b', false, 2), (2, 'a', true, 2),
///     ])
///     .into_ncw(0);
/// assert!(ncw.accepts(upw!("ab", "a")) && ncw.accepts(upw!("b")));
/// assert!(!ncw.accepts(upw!("ab")));
/// ```
pub type NCW<T = NTS<CharAlphabet, Void, bool>> = Automaton<T, Existential<CoBuchiCondition>>;

/// A history-deterministic co-Büchi automaton, an [`NCW`] whose nondeterminism can be resolved on
/// the fly, see [`HistoryDeterministic`].
pub type HDCW<T = NTS<CharAlphabet, Void, bool>> =
    Automaton<T, HistoryDeterministic<CoBuchiCondition>>;
