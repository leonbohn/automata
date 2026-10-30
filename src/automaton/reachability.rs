use super::semantics::observe_finite;
use super::{Automaton, Semantics, StatesWithColor};
use crate::alphabet::CharAlphabet;
use crate::representation::CollectPointed;
use crate::ts::States;
use crate::ts::operations::{DefaultIfMissing, Product, ProductIndex};
use crate::ts::run::ReachedStateColor;
use crate::ts::{Deterministic, StateIndex, SymbolOf, operations};
use crate::word::FiniteWord;
use crate::{Congruence, DTS, Pointed, TransitionSystem};
use crate::{Void, math};

/// Defines the [`Semantics`] that are used by a deterministic finite automaton
/// [`DFA`]. This leads to a [`crate::word::FiniteWord`] being accepted if the state that it reaches
/// is colored with `true`, and the word being rejected otherwise.
#[derive(Clone, Copy, Default, Hash, Eq, PartialEq)]
pub struct ReachabilityCondition;

impl std::fmt::Debug for ReachabilityCondition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DFA (reach true)")
    }
}

impl<T, W> Semantics<T, W> for ReachabilityCondition
where
    T: Deterministic<StateColor = bool>,
    W: FiniteWord<Symbol = SymbolOf<T>>,
{
    type Output = bool;
    type Observer = ReachedStateColor<T>;
    fn observe(
        &self,
        ts: &T,
        initial: StateIndex<T>,
        word: W,
    ) -> Option<<Self::Observer as crate::ts::run::Observer<T>>::Current> {
        observe_finite::<T, W, Self::Observer>(ts, initial, word)
    }
    fn evaluate(
        &self,
        observed: <Self::Observer as crate::ts::run::Observer<T>>::Current,
    ) -> Self::Output {
        observed
    }
}

/// A deterministic finite automaton (DFA) is a deterministic automaton with a simple acceptance condition. It accepts a finite word if it reaches an accepting state.
pub type DFA<T = DTS<CharAlphabet, bool, Void>> = Automaton<T, ReachabilityCondition>;

impl<D>
    DFA<
        operations::Recolor<
            D,
            operations::Provided<operations::DefaultIfMissing<D::StateIndex, bool>>,
        >,
    >
where
    D: Deterministic,
{
    /// Creates a new [`DFA`] from the given transition system and iterator over accepting
    /// states.
    ///
    /// # Example
    /// ```
    /// use automata::{automaton::DFA, ts::Builder};
    ///
    /// let ts = Builder::without_colors()
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
        let accepting: math::FxIndexMap<_, bool> = accepting_states
            .into_iter()
            .map(|idx| (idx, true))
            .collect();
        DFA::from(ts.with_state_color(DefaultIfMissing::new(accepting, false)))
    }
}

impl<D> DFA<D>
where
    D: Deterministic<StateColor = bool> + States,
{
    /// Returns true if and only if the given state is accepting, i.e.
    /// colored with `true`. Panics if no state with the given index exists.
    pub fn is_accepting(&self, state: StateIndex<Self>) -> bool {
        *self
            .state_color(state)
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
    /// the same language. If a DFA is incomplete, a word on which it has no run is rejected. Equivalent to [`Self::symmetric_difference_is_empty`].
    pub fn equivalent<E>(&self, other: E) -> bool
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool>,
    {
        self.symmetric_difference_is_empty(other)
    }

    /// Returns true if and only if the symmetric difference of the languages of `self` and `other`
    /// is empty. The product is explored lazily, so the search stops at the first reachable pair of
    /// states on which the two automata disagree.
    pub fn symmetric_difference_is_empty<E>(&self, other: E) -> bool
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool>,
    {
        self.product_witness(other, |a, b| a != b).is_none()
    }

    /// Returns a length-lexicographically minimal word that is accepted by exactly one of `self`
    /// and `other`, or `None` if the symmetric difference of their languages is empty.
    ///
    /// # Example
    /// ```
    /// use automata::{automaton::DFA, ts::Builder};
    ///
    /// let ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 0)])
    ///     .into_dts_with_initial(0);
    /// let ends_in_a = DFA::from_ts(&ts, [1]);
    /// let anything = DFA::from_ts(&ts, [0, 1]);
    /// assert_eq!(ends_in_a.symmetric_difference_word(&anything), Some(vec![]));
    /// assert_eq!(ends_in_a.symmetric_difference_word(&ends_in_a), None);
    /// ```
    pub fn symmetric_difference_word<E>(&self, other: E) -> Option<Vec<SymbolOf<Self>>>
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool>,
    {
        self.product_witness(other, |a, b| a != b)
    }

    /// Returns true if and only if the intersection of the languages of `self` and `other` is
    /// empty. Unlike `self.intersection(other).is_empty_language()`, this does not materialize
    /// the product and stops at the first reachable pair of accepting states.
    pub fn intersection_is_empty<E>(&self, other: E) -> bool
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool>,
    {
        self.product_witness(other, |a, b| a && b).is_none()
    }

    /// Finds a length-lexicographically minimal word leading to a reachable pair of states in the
    /// product of `self` and `other` whose colors satisfy `pred`. A missing edge leads to a
    /// rejecting sink, so words that only one of the automata can read are taken into account.
    fn product_witness<E>(
        &self,
        other: E,
        pred: impl Fn(bool, bool) -> bool,
    ) -> Option<Vec<SymbolOf<Self>>>
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool>,
    {
        type Pair<L, R> = (Option<L>, Option<R>);
        fn accepts<T: TransitionSystem<StateColor = bool>>(
            ts: &T,
            state: Option<T::StateIndex>,
        ) -> bool {
            state.is_some_and(|q| ts.state_color(q).is_some_and(|c| *c))
        }

        let start: Pair<StateIndex<Self>, E::StateIndex> =
            (Some(self.initial), Some(other.initial()));
        let symbols: Vec<_> = self.symbols().collect();
        let mut seen = math::FxIndexSet::default();
        seen.insert(start);
        // every entry is a pair together with the entry it was reached from and the symbol used
        let mut queue: Vec<(_, usize, Option<SymbolOf<Self>>)> = vec![(start, usize::MAX, None)];
        let mut next = 0;
        while next < queue.len() {
            let (pair, _, _) = queue[next];
            if pred(accepts(self, pair.0), accepts(&other, pair.1)) {
                let mut word = Vec::new();
                let mut at = next;
                while let (_, parent, Some(symbol)) = &queue[at] {
                    word.push(*symbol);
                    at = *parent;
                }
                word.reverse();
                return Some(word);
            }
            if pair != (None, None) {
                for &symbol in &symbols {
                    let target = (
                        pair.0.and_then(|q| self.successor(q, symbol)),
                        pair.1.and_then(|q| other.successor(q, symbol)),
                    );
                    if seen.insert(target) {
                        queue.push((target, next, Some(symbol)));
                    }
                }
            }
            next += 1;
        }
        None
    }

    /// Tries to construct a (finite) word witnessing that the accepted language is empty. If such a word exists,
    /// the function returns it, otherwise `None`.
    pub fn give_word(&self) -> Option<Vec<SymbolOf<Self>>> {
        self.minimal_representatives_iter().find_map(|rep| {
            if *self
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
    ) -> DFA<impl Deterministic<Alphabet = D::Alphabet, StateColor = bool> + States + 'a>
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool> + 'a,
    {
        let other_initial = other.initial();
        self.ts_product(other)
            .map_state_colors(|(a, b)| a || b)
            .with_initial(ProductIndex(self.initial, other_initial))
            .reachable_part()
            .collect_dfa()
    }

    /// Computes the intersection of `self` with the given `other` object (that can be viewed as a DFA) through
    /// a simple product construction.
    pub fn intersection<'a, E>(
        &'a self,
        other: E,
    ) -> DFA<impl Deterministic<Alphabet = D::Alphabet, StateColor = bool> + States + 'a>
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool> + 'a,
    {
        let other_initial = other.initial();
        self.ts_product(other)
            .map_state_colors(|(a, b)| a && b)
            .with_initial(ProductIndex(self.initial, other_initial))
            .reachable_part()
            .collect_dfa()
    }

    /// Computes the negation of `self` by swapping accepting and non-accepting states.
    pub fn negation(
        &self,
    ) -> DFA<impl Deterministic<Alphabet = D::Alphabet, StateColor = bool> + States + '_> {
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
    use crate::ts::Builder;

    #[test]
    fn equivalence_of_incomplete_dfas_counts_missing_runs_as_rejecting() {
        let edges = [(0, 'a', 0), (1, 'a', 2)];
        let from = |initial| {
            Builder::without_colors()
                .with_edges(edges)
                .into_dts_with_initial(initial)
        };
        // `looping` accepts a^n for all n, `once` the words ε and a
        let looping = from(0);
        let once = from(1);
        let looping = DFA::from_ts(&looping, [0]);
        let once = DFA::from_ts(&once, [1, 2]);
        assert!(!looping.equivalent(&once));
        assert_eq!(
            looping.symmetric_difference_word(&once),
            Some(vec!['a', 'a'])
        );
        assert!(once.equivalent(&once));
    }

    #[test]
    fn equivalence_is_symmetric_and_checks_both_directions() {
        let ts = Builder::without_colors()
            .with_edges([(0, 'a', 0), (0, 'b', 1), (1, 'a', 0), (1, 'b', 1)])
            .into_dts_with_initial(0);
        let all = DFA::from_ts(&ts, [0, 1]);
        let some = DFA::from_ts(&ts, [0]);
        assert!(all.equivalent(&all));
        assert!(!all.equivalent(&some));
        assert!(!some.equivalent(&all));
        assert!(all.intersection_is_empty(DFA::from_ts(&ts, [])));
        assert!(!all.intersection_is_empty(&some));
        assert!(all.symmetric_difference_is_empty(&all));
        assert!(!all.symmetric_difference_is_empty(&some));
        assert_eq!(all.symmetric_difference_word(&all), None);
        // 'b' leads to state 1 which is only accepted by `all`
        assert_eq!(all.symmetric_difference_word(&some), Some(vec!['b']));
        assert_eq!(some.symmetric_difference_word(&all), Some(vec!['b']));
    }

    #[test]
    fn dfa_from_ts() {
        let ts = Builder::without_colors()
            .with_edges([(0, 'a', 0), (0, 'b', 1), (1, 'a', 0), (1, 'b', 1)])
            .into_dts_with_initial(0);

        assert!(DFA::from_ts(&ts, [0]).accepts(""));
        assert!(!DFA::from_ts(&ts, [1]).accepts("a"));
        assert!(!DFA::from_ts(ts, []).accepts("a"));
    }
}
