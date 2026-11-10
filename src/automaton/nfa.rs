use super::{Automaton, DFA, Existential, ReachabilityCondition};
use crate::alphabet::{Alphabet, CharAlphabet};
use crate::representation::IntoTransitions;
use crate::ts::StateId;
use crate::ts::States;
use crate::ts::operations::{Determinize, merge_parallel_edges};
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
        let dfa = Determinize::on(self)
            .run()
            .into_dts()
            .map_state_colors(|subset| subset.into_iter().any(|accepting| accepting))
            .erase_edge_colors()
            .collect::<NTS<T::Alphabet, bool, Void>>();
        // as Spot does after its powerset construction
        // the edges of a state are labeled by disjoint expressions, no overlap check is needed
        DFA::from_parts(merge_parallel_edges(crate::ts::Det(dfa)), StateId::from(0))
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

    fn edge_count<T: crate::TransitionSystem<StateIndex = crate::ts::StateId>>(
        ts: &T,
        states: usize,
    ) -> usize {
        (0..states)
            .map(|q| {
                ts.edges_from(crate::ts::q(q as u32))
                    .map_or(0, |e| e.count())
            })
            .sum()
    }

    fn prop_nfa()
    -> crate::automaton::NFA<crate::NTS<crate::alphabet::PropAlphabet, bool, crate::Void>> {
        use crate::alphabet::{PropAlphabet, PropExpression};
        use crate::automaton::NFA;
        use crate::ts::{ForAlphabet, Sproutable};
        use crate::{NTS, Void};

        // overlapping labels over seven propositions, enough for the letter classes to be used
        let alphabet = PropAlphabet::<u32>::from_apnames(["p", "q", "r", "s", "t", "u", "v"]);
        let mut ts = NTS::<PropAlphabet, bool, Void>::for_alphabet(alphabet.clone());
        let states: Vec<_> = [false, false, true].map(|c| ts.add_state(c)).to_vec();
        for (from, label, to) in [
            (0, "0", 0),
            (0, "!0 | 1", 1),
            (0, "t", 0),
            (1, "2", 2),
            (1, "0 & !2", 1),
            (2, "!1", 0),
        ] {
            ts.add_edge((
                states[from],
                PropExpression::new(7, label),
                Void,
                states[to],
            ));
        }
        NFA::from_parts(ts, states[0])
    }

    #[test]
    fn determinize_over_propositional_letter_classes_agrees_with_nfa() {
        use crate::alphabet::{Alphabet, PropSymbol};

        let nfa = prop_nfa();
        let alphabet = crate::TransitionSystem::alphabet(&nfa).clone();
        let dfa = nfa.determinize();
        // merging leaves far fewer edges than there are atoms
        let unmerged = crate::ts::operations::Determinize::on(&nfa).run();
        let n = crate::ts::States::state_count(&dfa);
        assert_eq!(n, crate::ts::States::state_count(unmerged.ts()));
        assert!(edge_count(dfa.ts(), n) < edge_count(unmerged.ts(), n));
        let symbols: Vec<PropSymbol<u32>> = alphabet.universe().collect();
        let mut words: Vec<Vec<PropSymbol<u32>>> = vec![vec![]];
        for _ in 0..2 {
            let longer: Vec<_> = words
                .iter()
                .flat_map(|w| {
                    symbols.iter().map(|&s| {
                        let mut w = w.clone();
                        w.push(s);
                        w
                    })
                })
                .collect();
            words.extend(longer);
        }
        for w in &words {
            assert_eq!(nfa.accepts(w), dfa.accepts(w), "{w:?}");
        }
    }
}
