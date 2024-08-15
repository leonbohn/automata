use automata::{math::Set, prelude::*, random, transition_system::path};
use itertools::Itertools;
use tracing::{info, warn};

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    path::Iter,
};

use crate::prefixtree::prefix_tree;

use super::{consistency::ConsistencyCheck, OmegaSample};

pub enum SproutError<A: ConsistencyCheck<WithInitial<DTS>>> {
    Threshold(usize, A::Aut, WithInitial<DTS>),
    Timeout(WithInitial<DTS>),
}

impl<A: ConsistencyCheck<WithInitial<DTS>>> Debug for SproutError<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SproutError::Threshold(thresh, _default, ts) => {
                write!(f, "exceeded threshold {thresh} with size {}", ts.size())
            }
            SproutError::Timeout(ts) => write!(f, "ran into timeout with ts of size {}", ts.size()),
        }
    }
}

/// gives a deterministic acc_type omega automaton that is consistent with the given sample
/// implements the sprout passive learning algorithm for omega automata from <https://arxiv.org/pdf/2108.03735.pdf>
/// missing transitions are processed in length-lexicographi order.
/// the sample has no direct influence on this order.
pub fn sprout<A: ConsistencyCheck<WithInitial<DTS>>>(
    sample: OmegaSample,
    acc_type: A,
) -> Result<A::Aut, SproutError<A>> {
    let time_start = std::time::Instant::now();

    // make ts with initial state
    let mut ts = Automaton::new_with_initial_color(sample.alphabet().clone(), Void);

    // compute threshold
    let (lb, le) = sample
        .words()
        .map(|w| (w.spoke().len(), w.cycle().len()))
        .fold((0, 0), |(a0, a1), (b0, b1)| (a0.max(b0), a1.max(b1)));
    let thresh = (lb + le.pow(2) + 1) as isize;
    info!("starting sprout with threshold {thresh}");

    // while there are positive sample words that are escaping
    let mut pos_sets = vec![];
    let mut neg_sets = vec![];
    let mut mut_sample = sample.clone();
    let mut source: u32 = 0;
    'outer: while source < ts.size() as u32 {
        // WARN TODO should find a way to either pass or globally set timeout
        if time_start.elapsed() >= std::time::Duration::from_secs(60 * 30) {
            warn!(
                "task exceeded timeout, aborting with automaton of size {}",
                ts.size()
            );
            return Err(SproutError::Timeout(ts));
        }
        // let u = escape_prefix[..escape_prefix.len() - 1].to_string();
        // let a = escape_prefix.chars().last().expect("empty escape prefix");
        // check thresh
        let mr = ts.minimal_representative(source).unwrap();
        if mr.len() as isize > (thresh + 1) {
            // compute default automaton
            return Err(SproutError::Threshold(
                thresh as usize,
                acc_type.default_automaton(&sample),
                ts,
            ));
        }
        // let source = ts.finite_run(&u).unwrap().reached();
        'inner: for a in sample.alphabet().universe() {
            for q in ts.state_indices_vec() {
                // try adding transition
                ts.add_edge((source, a, Void, q));
                // continue if consistent
                let (is_consistent, pos_sets_new, neg_sets_new) =
                    acc_type.consistent(&ts, &mut_sample, pos_sets.clone(), neg_sets.clone());
                if is_consistent {
                    // update already known infinity sets
                    pos_sets = pos_sets_new;
                    neg_sets = neg_sets_new;
                    mut_sample.remove_non_escaping(&ts);
                    continue 'inner;
                } else {
                    ts.remove_edges_from_matching(source, a);
                }
            }
            // if none consistent add new state
            let new_state = ts.add_state(Void);
            ts.add_edge((source, a, Void, new_state));
        }
        source += 1;
    }
    Ok(acc_type.consistent_automaton(&ts, &mut_sample, pos_sets, neg_sets))
}

/// gives a deterministic acc_type omega automaton that is consistent with the given sample
/// implements the sprout passive learning algorithm for omega automata from <https://arxiv.org/pdf/2108.03735.pdf>
/// missing transitions are processed, if they correspond to an escape prefix of a positive example word
/// when no such words exist anymore, a rejecting sink is added to complete the automaton
pub fn sprout_escprf<A: ConsistencyCheck<WithInitial<DTS>>>(
    // pub fn sprout<A: ConsistencyCheck<WithInitial<DTS>>>(
    sample: OmegaSample,
    acc_type: A,
) -> Result<A::Aut, SproutError<A>> {
    let time_start = std::time::Instant::now();

    // make ts with initial state
    let mut ts = Automaton::new_with_initial_color(sample.alphabet().clone(), Void);

    // compute threshold
    let (lb, le) = sample
        .words()
        .map(|w| (w.spoke().len(), w.cycle().len()))
        .fold((0, 0), |(a0, a1), (b0, b1)| (a0.max(b0), a1.max(b1)));
    let thresh = (lb + le.pow(2) + 1) as isize;
    info!("starting sprout with threshold {thresh}");

    // while there are positive sample words that are escaping
    let mut pos_sets = vec![];
    let mut neg_sets = vec![];
    let mut mut_sample = sample.clone();
    'outer: while let Some(escape_prefix) =
        length_lexicographical_sort(ts.escape_prefixes(mut_sample.positive_words()).collect())
            .first()
    {
        // WARN TODO should find a way to either pass or globally set timeout
        if time_start.elapsed() >= std::time::Duration::from_secs(60 * 30) {
            warn!(
                "task exceeded timeout, aborting with automaton of size {}",
                ts.size()
            );
            return Err(SproutError::Timeout(ts));
        }
        let u = escape_prefix[..escape_prefix.len() - 1].to_string();
        let a = escape_prefix.chars().last().expect("empty escape prefix");
        // check thresh
        if (u.len() as isize) - 1 > thresh {
            // compute default automaton
            return Err(SproutError::Threshold(
                thresh as usize,
                acc_type.default_automaton(&sample),
                ts,
            ));
        }
        let source = ts.finite_run(&u).unwrap().reached();
        for q in ts.state_indices_vec() {
            // try adding transition
            ts.add_edge((source, a, Void, q));
            // continue if consistent
            let (is_consistent, pos_sets_new, neg_sets_new) =
                acc_type.consistent(&ts, &mut_sample, pos_sets.clone(), neg_sets.clone());
            if is_consistent {
                // update already known infinity sets
                pos_sets = pos_sets_new;
                neg_sets = neg_sets_new;
                mut_sample.remove_non_escaping(&ts);
                continue 'outer;
            } else {
                ts.remove_edges_from_matching(source, a);
            }
        }
        // if none consistent add new state
        let new_state = ts.add_state(Void);
        ts.add_edge((source, a, Void, new_state));
    }
    Ok(acc_type.consistent_automaton(&ts, &mut_sample, pos_sets, neg_sets))
}

/// gives a deterministic acc_type omega automaton that is consistent with the given sample
/// implements the sprout passive learning algorithm for omega automata from <https://arxiv.org/pdf/2108.03735.pdf>
/// all possible target transitioins are tested and ou of all such states that preserve consistency,
/// the one is chosen, which minimizes the number of escaping words in the sample
pub fn sprout_minesc<A: ConsistencyCheck<WithInitial<DTS>>>(
    sample: OmegaSample,
    acc_type: A,
) -> Result<A::Aut, SproutError<A>> {
    let time_start = std::time::Instant::now();

    // make ts with initial state
    let mut ts = Automaton::new_with_initial_color(sample.alphabet().clone(), Void);

    // compute threshold
    let (lb, le) = sample
        .words()
        .map(|w| (w.spoke().len(), w.cycle().len()))
        .fold((0, 0), |(a0, a1), (b0, b1)| (a0.max(b0), a1.max(b1)));
    let thresh = (lb + le.pow(2) + 1) as isize;
    info!("starting sprout with threshold {thresh}");

    // while there are positive sample words that are escaping
    let mut pos_sets = vec![];
    let mut neg_sets = vec![];
    let mut mut_sample = sample.clone();
    'outer: while let Some(escape_prefix) =
        length_lexicographical_sort(ts.escape_prefixes(mut_sample.positive_words()).collect())
            .first()
    {
        // WARN TODO should find a way to either pass or globally set timeout
        if time_start.elapsed() >= std::time::Duration::from_secs(60 * 30) {
            warn!(
                "task exceeded timeout, aborting with automaton of size {}",
                ts.size()
            );
            return Err(SproutError::Timeout(ts));
        }
        let u = escape_prefix[..escape_prefix.len() - 1].to_string();
        let a = escape_prefix.chars().last().expect("empty escape prefix");
        // check thresh
        if (u.len() as isize) - 1 > thresh {
            // compute default automaton
            return Err(SproutError::Threshold(
                thresh as usize,
                acc_type.default_automaton(&sample),
                ts,
            ));
        }
        let source = ts.finite_run(&u).unwrap().reached();
        let mut min_target: Option<u32> = None;
        let mut min_escapes = sample.words.len() + 1;
        for q in ts.state_indices_vec() {
            // try adding transition
            ts.add_edge((source, a, Void, q));
            // continue if consistent
            let (is_consistent, pos_sets_new, neg_sets_new) =
                acc_type.consistent(&ts, &mut_sample, pos_sets.clone(), neg_sets.clone());
            if is_consistent {
                // save number of escaping words in hash map
                let num_successful = sample
                    .words()
                    .filter(|word| ts.omega_run(word).is_ok())
                    .count();
                if num_successful < min_escapes {
                    min_target = Some(q);
                    min_escapes = num_successful;
                }
            }
            ts.remove_edges_from_matching(source, a);
        }
        if let Some(target) = min_target {
            // choose consistent target that minimizes escapes
            ts.add_edge((source, a, Void, target));
            // and update already known infinity sets
            let (is_consistent, pos_sets_new, neg_sets_new) =
                acc_type.consistent(&ts, &mut_sample, pos_sets.clone(), neg_sets.clone());
            pos_sets = pos_sets_new;
            neg_sets = neg_sets_new;
            mut_sample.remove_non_escaping(&ts);
        } else {
            // if none consistent add new state
            let new_state = ts.add_state(Void);
            ts.add_edge((source, a, Void, new_state));
        }
    }
    Ok(acc_type.consistent_automaton(&ts, &mut_sample, pos_sets, neg_sets))
}

/// sort a vector of Strings length lexicographically
pub fn length_lexicographical_sort(mut words: Vec<String>) -> Vec<String> {
    words.sort_by(|a, b| {
        // Compare by length first
        let length_comparison = a.len().cmp(&b.len());

        // If lengths are equal, compare lexicographically
        if length_comparison == std::cmp::Ordering::Equal {
            a.cmp(b)
        } else {
            length_comparison
        }
    });
    words
}

impl OmegaSample {
    /// Remove all words from the sample that are not escaping in the given transition system
    pub fn remove_non_escaping<T>(&mut self, ts: &T)
    where
        T: TransitionSystem<Alphabet = CharAlphabet, StateIndex = u32> + Deterministic + Pointed,
        // <T as TransitionSystem>::EdgeColor: Eq + std::hash::Hash,
    {
        // run transition system on sample words and
        // separate in escaping and non-escaping (successful) runs
        let pos_successful: Vec<_> = self
            .positive_words()
            .filter(|word| ts.omega_run(word).is_ok())
            .cloned()
            .collect();
        for w in pos_successful {
            self.remove(&w);
        }

        let neg_successful: Vec<_> = self
            .negative_words()
            .filter(|word| ts.omega_run(word).is_ok())
            .cloned()
            .collect();
        for w in neg_successful {
            self.remove(&w);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::passive::OmegaSample;
    use automata::prelude::*;

    #[test]
    fn sprout_buchi() {
        let sigma = CharAlphabet::of_size(2);

        // build sample
        let sample =
            OmegaSample::new_omega_from_pos_neg(sigma, [upw!("a"), upw!("a", "b")], [upw!("b")]);

        // build dba
        let dba = DTS::builder()
            .with_transitions([
                (0, 'a', true, 1),
                (1, 'a', true, 0),
                (1, 'b', true, 1),
                (0, 'b', false, 2),
                (2, 'a', false, 2),
                (2, 'b', false, 2),
            ])
            .default_color(Void)
            .into_dba(0);

        let res = sprout(sample, BuchiCondition).unwrap();
        assert_eq!(res, dba);
    }

    #[test]
    fn sprout_buchi_thresh() {
        let sigma = CharAlphabet::of_size(2);

        // build sample
        let sample = OmegaSample::new_omega_from_pos_neg(
            sigma,
            [upw!("a"), upw!("baa")],
            [upw!("ab"), upw!("ba"), upw!("babaa"), upw!("baaba")],
        );

        // build dba
        let mut dba = DTS::builder()
            .with_transitions([
                (0, 'a', true, 1),
                (0, 'b', true, 2),
                (1, 'a', true, 1),
                (1, 'b', false, 5),
                (2, 'a', true, 3),
                (2, 'b', false, 5),
                (3, 'a', true, 4),
                (3, 'b', false, 5),
                (4, 'b', true, 2),
                (4, 'a', false, 5),
                (5, 'a', false, 5),
                (5, 'b', false, 5),
            ])
            .default_color(Void)
            .into_dba(0);

        let res = sprout(sample, BuchiCondition).err();
        assert!(matches!(res.unwrap(), SproutError::Threshold(_, _, _)))
    }

    #[test]
    fn llex_sort() {
        assert_eq!(
            length_lexicographical_sort(vec![
                String::from("ca"),
                String::from("ac"),
                String::from("aaa"),
                String::from("b")
            ]),
            vec![
                String::from("b"),
                String::from("ac"),
                String::from("ca"),
                String::from("aaa")
            ]
        );
    }

    #[test]
    fn sprout_parity() {
        let sigma = CharAlphabet::of_size(2);

        // build sample
        let sample = OmegaSample::new_omega_from_pos_neg(
            sigma,
            [upw!("a"), upw!("aab")],
            [upw!("b"), upw!("abb")],
        );

        // build dba
        let dpa = DTS::builder()
            .with_transitions([
                (0, 'a', 0, 0),
                (0, 'b', 0, 1),
                (1, 'a', 0, 0),
                (1, 'b', 1, 2),
                (2, 'a', 1, 2),
                (2, 'b', 1, 2),
            ])
            .default_color(Void)
            .into_dpa(0);

        let res = sprout(sample, MinEvenParityCondition).unwrap();
        assert_eq!(res, dpa);
    }

    #[test]
    fn sprout_parity_thresh() {
        let sigma = CharAlphabet::of_size(2);

        // build sample
        let sample = OmegaSample::new_omega_from_pos_neg(
            sigma,
            [upw!("a"), upw!("baaa")],
            [upw!("ba"), upw!("baa")],
        );

        // build dba
        let mut dpa = DTS::builder()
            .with_transitions([
                (0, 'a', 0, 1),
                (1, 'a', 0, 1),
                (0, 'b', 0, 2),
                (2, 'a', 0, 3),
                (3, 'a', 0, 4),
                (4, 'a', 0, 5),
                (5, 'b', 0, 2),
            ])
            .default_color(Void)
            .into_dpa(0);
        dpa.complete_with_colors(Void, 1);

        let res = sprout(sample, MinEvenParityCondition).err();
        assert!(matches!(res.unwrap(), SproutError::Threshold(_, _, _)))
    }
}
