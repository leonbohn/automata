use std::collections::VecDeque;

use crate::alphabet::Alphabet;
use crate::math;
use crate::ts::{Sproutable, StateId};
use crate::word::{OmegaWord, ReducedOmegaWord};
use crate::{DTS, Void};
use crate::{Pointed, RightCongruence};
use itertools::Itertools;
use tracing::trace;

pub fn prefix_tree<A: Alphabet, W: Into<ReducedOmegaWord<A::Symbol>>, I: IntoIterator<Item = W>>(
    alphabet: A,
    words: I,
) -> RightCongruence<DTS<A, Vec<A::Symbol>>> {
    let words: Vec<ReducedOmegaWord<_>> = words.into_iter().map(|word| word.into()).collect_vec();
    debug_assert!(words.iter().all(|word| !word.raw_word().is_empty()));
    fn build_accepting_loop<A: Alphabet>(
        alphabet: &A,
        tree: &mut RightCongruence<DTS<A, Vec<A::Symbol>>>,
        state: StateId,
        access: Vec<A::Symbol>,
        loop_segment: &[A::Symbol],
    ) {
        let mut access = access;
        let mut current = state;
        for symbol in &loop_segment[..loop_segment.len() - 1] {
            access.push(*symbol);
            trace!("adding state {:?}", access);
            let next = tree.add_state(access.clone());
            tree.add_edge((current, alphabet.make_expression(*symbol), Void, next));
            current = next;
        }
        tree.add_edge((
            current,
            alphabet.make_expression(loop_segment[loop_segment.len() - 1]),
            state,
        ));
    }
    let mut tree = RightCongruence::new_with_initial_color(alphabet.clone(), vec![]);
    let root = tree.initial();

    let mut queue = VecDeque::from_iter([(root, vec![], words.to_vec())]);

    while let Some((state, access, words)) = queue.pop_front() {
        debug_assert!(!words.is_empty());
        debug_assert!(words.iter().all(|word| !word.raw_word().is_empty()));
        if words.len() == 1 && words[0].loop_index() == 0 {
            build_accepting_loop(&alphabet, &mut tree, state, access, words[0].cycle());
        } else {
            let mut map: math::FxIndexMap<_, math::FxIndexSet<_>> = math::FxIndexMap::default();
            for mut word in words {
                let sym = word.pop_front();
                debug_assert!(
                    !word.raw_word().is_empty(),
                    "popping front lead to empty representation"
                );

                map.entry(sym).or_default().insert(word);
            }

            for sym in alphabet.universe() {
                if let Some(new_words) = map.swap_remove(&sym) {
                    debug_assert!(!new_words.is_empty());
                    let new_access = access
                        .iter()
                        .cloned()
                        .chain(std::iter::once(sym))
                        .collect_vec();
                    let successor = tree.add_state(new_access.clone());
                    tree.add_edge((state, alphabet.make_expression(sym), successor));
                    queue.push_back((successor, new_access, new_words.into_iter().collect()));
                }
            }
        }
    }

    tree
}

#[cfg(test)]
mod tests {
    use super::prefix_tree;
    use crate::alphabet::CharAlphabet;
    use crate::ts::Deterministic;

    #[test]
    fn build_prefix_tree() {
        let words = [upw!("aa"), upw!("aba"), upw!("bbaab"), upw!("bb")];
        let alphabet = CharAlphabet::from_iter(['a', 'b']);
        let pta = prefix_tree(alphabet, words.clone());
        // all words of the tree have a run that does not leave it
        for word in &words {
            assert!(pta.run(word).is_successful());
        }
        // everything else leaves the tree
        for word in ["ba", "bbbbbbbbba", "ababababbbabaababa", "aaaaaaaaaaaaab"] {
            assert_eq!(pta.reached_state(word), None);
        }
    }
}
