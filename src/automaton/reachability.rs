use super::{FiniteWordAutomaton, Semantics, StatesWithColor};
use crate::representation::CollectTs;
use crate::ts::operations::{DefaultIfMissing, Product, ProductIndex};
use crate::ts::run::ReachedStateColor;
use crate::ts::{Deterministic, EdgeColor, StateIndex, SymbolOf, operations};
use crate::{Congruence, DTS, Pointed, TransitionSystem};
use automata_core::alphabet::CharAlphabet;
use automata_core::{Void, math};

/// Defines the [`Semantics`] that are used by a deterministic finite automaton
/// [`DFA`]. This leads to a [`crate::core::word::FiniteWord`] being accepted if the state that it reaches
/// is colored with `true`, and the word being rejected otherwise.
#[derive(Clone, Copy, Default, Hash, Eq, PartialEq)]
pub struct ReachabilityCondition;

impl std::fmt::Debug for ReachabilityCondition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DFA (reach true)")
    }
}

impl<T: Deterministic<StateColor = bool>> Semantics<T, false> for ReachabilityCondition {
    type Output = bool;
    type Observer = ReachedStateColor<T>;
    fn evaluate(
        &self,
        observed: <Self::Observer as crate::ts::run::Observer<T>>::Current,
    ) -> Self::Output {
        observed
    }
}

/// A deterministic finite automaton (DFA) is a deterministic automaton with a simple acceptance condition. It accepts a finite word if it reaches an accepting state.
pub type DFA<A = CharAlphabet, C = Void, D = DTS<A, bool, C>> =
    FiniteWordAutomaton<A, ReachabilityCondition, bool, C, true, D>;

/// Helper trait for creating a [`DFA`] from a given transition system.
pub type IntoDFA<T> = DFA<<T as TransitionSystem>::Alphabet, EdgeColor<T>, T>;

impl<D> IntoDFA<operations::WithStateColor<D, operations::DefaultIfMissing<D::StateIndex, bool>>>
where
    D: Deterministic,
{
    /// Creates a new [`DFA`] from the given transition system and iterator over accepting
    /// states.
    ///
    /// # Example
    /// ```
    /// use automata::{automaton::DFA, ts::TSBuilder};
    ///
    /// let ts = TSBuilder::without_colors()
    ///     .with_edges([(0, 'a', 0), (0, 'b', 1), (1, 'a', 0), (1, 'b', 1)])
    ///     .into_dts_with_initial(0);
    /// assert!(DFA::from_ts(&ts, [0]).accepts(""));
    /// assert!(!DFA::from_ts(&ts, [1]).accepts("a"));
    /// assert!(!DFA::from_ts(ts, []).accepts("a"));
    /// ```
    pub fn from_ts(ts: D, accepting_states: impl IntoIterator<Item = D::StateIndex>) -> Self
    where
        D: Pointed,
    {
        let accepting: math::Map<_, bool> = accepting_states
            .into_iter()
            .map(|idx| (idx, true))
            .collect();
        DFA::from(ts.with_state_color(DefaultIfMissing::new(accepting, false)))
    }
}

impl<D> IntoDFA<D>
where
    D: Deterministic<StateColor = bool>,
{
    /// Returns true if and only if the given state is accepting, i.e.
    /// colored with `true`. Panics if no state with the given index exists.
    pub fn is_accepting(&self, state: StateIndex<Self>) -> bool {
        self.state_color(state)
            .expect("can only be called for states that exist!")
    }

    /// Returns the indices of all states that are accepting.
    pub fn accepting_states(&self) -> StatesWithColor<'_, Self> {
        StatesWithColor::new(self, true)
    }

    /// Returns the indices of all states that are rejecting.
    pub fn rejecting_states(&self) -> StatesWithColor<'_, Self> {
        StatesWithColor::new(self, false)
    }

    /// Checks whether `self` is equivalent to `other`, i.e. whether the two DFAs accept
    /// the same language. This is done by negating `self` and then verifying that the intersection
    /// of the negated automaton with `other` is empty.
    pub fn equivalent<E>(&self, other: E) -> bool
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool>,
    {
        self.negation().intersection(other).is_empty_language()
    }

    /// Tries to construct a (finite) word witnessing that the accepted language is empty. If such a word exists,
    /// the function returns it, otherwise `None`.
    pub fn give_word(&self) -> Option<Vec<SymbolOf<Self>>> {
        self.minimal_representatives_iter().find_map(|rep| {
            if self
                .state_color(rep.state_index())
                .expect("Every state must be colored")
            {
                Some(rep.decompose().0)
            } else {
                None
            }
        })
    }

    /// Returns true if and only if the accepted language is empty.
    pub fn is_empty_language(&self) -> bool {
        self.give_word().is_none()
    }

    /// Computes the union of `self` with the given `other` object (that can be viewed as a DFA) through
    /// a simple product construction.
    pub fn union<'a, E>(
        &'a self,
        other: E,
    ) -> IntoDFA<impl Deterministic<Alphabet = D::Alphabet, StateColor = bool> + 'a>
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool> + 'a,
    {
        let other_initial = other.initial();
        self.ts_product(other)
            .map_state_colors(|(a, b)| a || b)
            .with_initial(ProductIndex(self.initial, other_initial))
            .collect_dfa()
    }

    /// Computes the intersection of `self` with the given `other` object (that can be viewed as a DFA) through
    /// a simple product construction.
    pub fn intersection<'a, E>(
        &'a self,
        other: E,
    ) -> IntoDFA<impl Deterministic<Alphabet = D::Alphabet, StateColor = bool> + 'a>
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool> + 'a,
    {
        let other_initial = other.initial();
        self.ts_product(other)
            .map_state_colors(|(a, b)| a && b)
            .with_initial(ProductIndex(self.initial, other_initial))
            .collect_dfa()
    }

    /// Computes the negation of `self` by swapping accepting and non-accepting states.
    pub fn negation(
        &self,
    ) -> IntoDFA<impl Deterministic<Alphabet = D::Alphabet, StateColor = bool> + '_> {
        self.map_state_colors(|x| !x)
            .with_initial(self.initial)
            .collect_dfa()
    }

    /// Attempts to separate the state `left` from the state `right` by finding a word that leads to different colors.
    /// For a [`DFA`], this means that the returned word is in the symmetric difference of
    /// the languages accepted by the two states.
    pub fn separate(
        &self,
        left: StateIndex<Self>,
        right: StateIndex<Self>,
    ) -> Option<Vec<SymbolOf<Self>>> {
        if right == left {
            return None;
        }

        self.with_initial(left)
            .ts_product(self.with_initial(right))
            .minimal_representatives_iter()
            .find_map(|rep| {
                let ProductIndex(l, r) = rep.state_index();
                if self.state_color(l).unwrap() != self.state_color(r).unwrap() {
                    Some(rep.into_inner())
                } else {
                    None
                }
            })
    }
}

#[cfg(test)]
mod tests {
    use crate::automaton::DFA;
    use crate::ts::TSBuilder;

    #[test]
    fn dfa_from_ts() {
        let ts = TSBuilder::without_colors()
            .with_edges([(0, 'a', 0), (0, 'b', 1), (1, 'a', 0), (1, 'b', 1)])
            .into_dts_with_initial(0);

        assert!(DFA::from_ts(&ts, [0]).accepts(""));
        assert!(!DFA::from_ts(&ts, [1]).accepts("a"));
        assert!(!DFA::from_ts(ts, []).accepts("a"));
    }
}
