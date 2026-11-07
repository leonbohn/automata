use crate::{Color, Int, Void, alphabet::CharAlphabet, math};

use crate::automaton::semantics::observe_omega;
use crate::automaton::{Automaton, Semantics};
use crate::automaton::{CycleCondition, Existential, HistoryDeterministic};
use crate::ts::{Deterministic, EdgeColor, StateIndex, SymbolOf, run};
use crate::word::OmegaWord;
use crate::{DTS, NTS};

/// A deterministic Muller automaton (DMA) uses a [`MullerCondition`] to determine acceptance.
/// Such a condition consists of a set of sets of colors. It considers an infinite run to
/// be accepting, if the set of colors that appear infinitely often in the run is an element
/// of the [`MullerCondition`]. In other words such a Muller condition lists out precisely
/// the sets of colors that are allowed to appear infinitely often in an accepting run. Note,
/// that this means if a run is not accepting, then the set of colors it visits infinitely
/// often is not contained in the [`MullerCondition`]. This allows for easy complementation
/// of a [`DMA`] by simply taking the complement of the [`MullerCondition`].
pub type DMA<T = DTS<CharAlphabet, Void, Int>> = Automaton<T, MullerCondition<EdgeColor<T>>>;

/// A nondeterministic Muller automaton (NMA): it accepts an infinite word if *some* run on it
/// satisfies the [`MullerCondition`], see [`Existential`]. Deciding this takes time exponential in
/// the number of colors in the worst case.
pub type NMA<T = NTS<CharAlphabet, Void, Int>> =
    Automaton<T, Existential<MullerCondition<EdgeColor<T>>>>;

/// A history-deterministic Muller automaton, an [`NMA`] whose nondeterminism can be resolved on
/// the fly, see [`HistoryDeterministic`].
pub type HDMA<T = NTS<CharAlphabet, Void, Int>> =
    Automaton<T, HistoryDeterministic<MullerCondition<EdgeColor<T>>>>;

/// A Muller condition over some [`Color`] `C` is a set of sets of elements of type `C`. It
/// is satisfied by a set (usually the set of colors that appear infinitely often in a run),
/// if it contains the set.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct MullerCondition<C: Color + Eq + std::hash::Hash>(Vec<math::FxIndexSet<C>>);

impl<C: Color + Ord + Eq + std::hash::Hash> MullerCondition<C> {
    /// Builds a new instance from an iterator that yields iterators that yield colors
    /// (or elements of type `C`).
    ///
    /// # Example
    /// ```
    /// use automata::automaton::MullerCondition;
    ///
    /// let condition = MullerCondition::from_iter_iter([[0], [1]]);
    ///
    /// assert!(!condition.satisfied_by_iter([0, 1]));
    /// assert!(condition.satisfied_by_iter([0]));
    /// assert!(condition.satisfied_by_iter([1, 1, 1]));
    /// ```
    pub fn from_iter_iter<I, J>(iter: I) -> Self
    where
        I: IntoIterator<Item = J>,
        J: IntoIterator<Item = C>,
    {
        Self(iter.into_iter().map(|x| x.into_iter().collect()).collect())
    }

    /// Returns `true` if the given `set` of colors satisfies this condition,
    /// i.e. if `self` contains `set`.
    pub fn satisfied_by_set(&self, set: &math::FxIndexSet<C>) -> bool {
        self.0.contains(set)
    }

    /// Returns `true` if the set of colors yielded by `iter` satisfy this condition.
    pub fn satisfied_by_iter<I: IntoIterator<Item = C>>(&self, iter: I) -> bool {
        self.satisfied_by_set(&iter.into_iter().collect())
    }

    /// Creates a new instance from a set of sets of colors.
    pub fn new(sets: Vec<math::FxIndexSet<C>>) -> Self {
        Self(sets)
    }
}

impl<T, W> Semantics<T, W> for MullerCondition<EdgeColor<T>>
where
    T: Deterministic<EdgeColor: Eq + std::hash::Hash>,
    W: OmegaWord<Symbol = SymbolOf<T>>,
{
    type Output = bool;
    fn output(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<bool> {
        let inf = observe_omega::<T, W, run::EdgeColorSet<T>>(ts, initial, word)?;
        Some(self.0.contains(&inf.0))
    }
}

impl<C: Color + Eq + std::hash::Hash> CycleCondition for MullerCondition<C> {
    type Color = C;
    fn satisfied_by(&self, colors: &math::FxIndexSet<C>) -> bool {
        self.0.contains(colors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::Builder;
    use crate::ts::q;

    #[test]
    fn muller_automaton() {
        let ts = Builder::without_state_colors()
            .with_transitions([
                (0, 'a', 0, 0),
                (0, 'b', 1, 1),
                (1, 'a', 0, 0),
                (1, 'b', 1, 1),
            ])
            .into_dts();
        let dra =
            DMA::from_parts_with_acceptance(ts, q(0), MullerCondition::from_iter_iter([[0], [1]]));

        assert!(dra.accepts(upw!("a")));
        assert!(dra.accepts(upw!("b")));
        assert!(!dra.accepts(upw!("ba")));
    }
}
