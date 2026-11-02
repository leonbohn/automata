use super::{Automaton, DFA, Semantics};
use crate::alphabet::{Alphabet, CharAlphabet, Matcher};
use crate::representation::IntoTransitions;
use crate::ts::States;
use crate::ts::operations::Determinize;
use crate::ts::run::Observer;
use crate::ts::{StateId, StateIndex, SymbolOf};
use crate::word::FiniteWord;
use crate::{DTS, NTS, TransitionSystem, Void};

/// The [`Semantics`] of a nondeterministic finite automaton [`NFA`]: a finite word is accepted if
/// *some* run on it ends in a state colored with `true`. Words are checked by tracking the set of
/// states that the runs can be in, so the cost is linear in the length of the word.
#[derive(Clone, Copy, Default, Hash, Eq, PartialEq)]
pub struct NfaCondition;

impl std::fmt::Debug for NfaCondition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NFA (some run reaches true)")
    }
}

/// Carries the verdict of [`NfaCondition`] as the [`Semantics::Observer`] type. A nondeterministic
/// system has no single run to observe, so this is no observer in the sense of running it step by
/// step: it only holds the result that [`NfaCondition`] computes with a subset simulation.
#[derive(Debug, Clone, Copy)]
pub struct SomeRunAccepts(bool);

impl<T: TransitionSystem> Observer<T> for SomeRunAccepts {
    type Current = bool;
    fn into_current(self) -> bool {
        self.0
    }
    fn merge(&mut self, later: Self) {
        self.0 = later.0;
    }
    fn begin(_: &T, _: StateIndex<T>) -> Self {
        Self(false)
    }
    fn observe_one(&mut self, _: &T, _: StateIndex<T>, _: SymbolOf<T>) -> Option<StateIndex<T>> {
        None
    }
}

impl<T, W> Semantics<T, W> for NfaCondition
where
    T: TransitionSystem<StateColor = bool>,
    W: FiniteWord<Symbol = SymbolOf<T>>,
{
    type Output = bool;
    type Observer = SomeRunAccepts;

    fn observe(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<bool> {
        let mut current = vec![initial];
        for sym in word.symbols() {
            let mut next = Vec::new();
            for q in current {
                for edge in ts.edges_from(q).into_iter().flatten() {
                    if sym.matches(edge.expression()) {
                        next.push(edge.target());
                    }
                }
            }
            next.sort_unstable();
            next.dedup();
            current = next;
        }
        Some(
            current
                .into_iter()
                .any(|q| ts.state_color(q).is_some_and(|c| *c)),
        )
    }

    fn evaluate(&self, observed: bool) -> bool {
        observed
    }
}

/// A nondeterministic finite automaton (NFA): a transition system that need not be
/// [`Deterministic`](crate::Deterministic) (by default an [`NTS`]) whose states are colored with
/// `true` (accepting) or `false`, see [`NfaCondition`]. Use [`NFA::determinize`] to obtain an
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
pub type NFA<T = NTS<CharAlphabet, bool, Void>> = Automaton<T, NfaCondition>;

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
