use super::{Automaton, DFA, Existential, HistoryDeterministic, ReachabilityCondition};
use crate::alphabet::{Alphabet, CharAlphabet};
use crate::representation::IntoTransitions;
use crate::ts::StateId;
use crate::ts::States;
use crate::ts::operations::Determinize;
use crate::{DTS, NTS, TransitionSystem, Void};

/// A nondeterministic finite automaton (NFA): a transition system that need not be
/// [`Deterministic`](crate::Deterministic) (by default an [`NTS`]) whose states are colored with
/// `true` (accepting) or `false`. It accepts a finite word if *some* run on it ends in an
/// accepting state, see [`Existential`] and [`ReachabilityCondition`]. Use [`NFA::determinize`] to obtain an
/// equivalent [`DFA`].
///
/// ```
/// use automata::prelude::*;
/// /// // words over {a, b} whose second to last symbol is an `a`
/// let nfa = Builder::without_edge_colors()
///     .with_state_colors([false, false, true])
///     .with_transitions([(0, 'a', 0), (0, 'b', 0), (0, 'a', 1), (1, 'a', 2), (1, 'b', 2)])
///     .into_nfa(0);
/// assert!(nfa.accepts("bab"));
/// assert!(!nfa.accepts("abb"));
///
/// let dfa = nfa.determinize();
/// assert!(dfa.accepts("bab") && !dfa.accepts("abb"));
/// let minimized = dfa.clone().minimize();
/// assert_eq!(minimized.state_count(), 4);
/// assert!(Equivalence::of(&dfa).and(&minimized).holds());
/// ```
pub type NFA<T = NTS<CharAlphabet, bool, Void>> = Automaton<T, Existential<ReachabilityCondition>>;

/// A history-deterministic finite automaton, an [`NFA`] whose nondeterminism can be resolved on
/// the fly, see [`HistoryDeterministic`].
pub type HDFA<T = NTS<CharAlphabet, bool, Void>> =
    Automaton<T, HistoryDeterministic<ReachabilityCondition>>;

impl<T> NFA<T>
where
    T: TransitionSystem<StateColor = bool>,
{
    /// Determinizes the NFA with the subset construction (see [`Determinize`]): a subset of
    /// states is accepting if it contains an accepting state. The result is complete and has the
    /// initial subset `{initial}` as initial state, but is not minimized.
    pub fn determinize(&self) -> DFA<DTS<T::Alphabet, bool, Void>>
    where
        T: States,
        T::Alphabet: Alphabet,
    {
        Determinize::on(self)
            .run()
            .into_dts()
            .map_state_colors(|subset| subset.into_iter().any(|accepting| accepting))
            .erase_edge_colors()
            .with_initial(StateId::from(0))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::ts::Builder;

    #[test]
    fn determinize_agrees_with_nfa() {
        // second to last symbol is an `a`
        let nfa = Builder::without_edge_colors()
            .with_state_colors([false, false, true])
            .with_transitions([
                (0, 'a', 0),
                (0, 'b', 0),
                (0, 'a', 1),
                (1, 'a', 2),
                (1, 'b', 2),
            ])
            .into_nfa(0);
        let dfa = nfa.determinize();
        let mut words = vec![String::new()];
        for _ in 0..6 {
            let longer: Vec<_> = words
                .iter()
                .flat_map(|w| ["a", "b"].map(|c| format!("{w}{c}")))
                .collect();
            words.extend(longer);
            words.sort();
            words.dedup();
        }
        for w in &words {
            let expected = w.len() >= 2 && w.as_bytes()[w.len() - 2] == b'a';
            assert_eq!(nfa.accepts(w.as_str()), expected, "{w}");
            assert_eq!(dfa.accepts(w.as_str()), expected, "{w}");
        }
    }
}
