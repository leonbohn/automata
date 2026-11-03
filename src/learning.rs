//! Passive and active learning of automata, moved here from the `automata-learning` crate
//! (imported by plain copy of commit `1ed4171` of its branch `phase1-baseline`).
//!
//! **Experimental:** there is no stability promise for this module until the next minor release.

/// The errors that the learning algorithms can return.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum LearningError {
    /// A learner exceeded its bound on the size of the result, which means that the input (for
    /// example a sample) is not consistent with any automaton of the requested kind.
    #[error("exceeded the threshold of {0} states")]
    Threshold(usize),
    /// A learner exceeded its time limit.
    #[error("exceeded the time limit")]
    Timeout,
    /// L* exceeded its iteration threshold.
    #[error("exceeded the threshold of {0} iterations")]
    IterationThreshold(usize),
    /// An oracle must be complete, i.e. it must have an output for every word.
    #[error("the oracle is not complete")]
    IncompleteOracle,
    /// The oracle returned a counterexample on which the hypothesis agrees with it.
    #[error("the counterexample is not a counterexample")]
    InvalidCounterexample,
    /// A precise DPA needs at least one and at most `max` priorities.
    #[error("a precise DPA needs between 1 and {max} priorities, but {used} are used")]
    Priorities {
        /// The number of priorities that are used.
        used: usize,
        /// The maximal number of priorities that is supported.
        max: usize,
    },
    /// The structure is not complete or does not belong to the family it is used with, so a
    /// transition or class that is needed does not exist.
    #[error("a required state, class or transition does not exist")]
    Incomplete,
    /// A word cannot be positive and negative at the same time.
    #[error("a word is classified as positive and as negative")]
    ConflictingClassification,
    /// The transition system is not consistent with the sample, so no automaton can be built
    /// from it.
    #[error("the transition system is not consistent with the sample")]
    Inconsistent,
}

/// Contains passive learners such as RPNI, DBAInf and DPAInf.
#[macro_use]
pub mod passive;

/// Deals with active learning algorithms such as L*.
pub mod active;
mod priority_mapping;
pub use priority_mapping::{AnnotatedCongruence, Annotation, WeakPriorityMapping};

pub(crate) mod prefixtree;

/// Strategies for the property tests of the learning algorithms.
#[cfg(test)]
mod properties {
    use crate::automaton::DFA;
    use crate::ts::Builder;
    use crate::{DTS, Void};
    use proptest::prelude::*;

    /// A complete DFA with 1 to 6 states over the alphabet `{a, b}`.
    pub fn dfa() -> impl Strategy<Value = DFA<DTS<crate::alphabet::CharAlphabet, bool, Void>>> {
        (1u32..=6).prop_flat_map(|n| {
            (
                proptest::collection::vec((0..n, 0..n, any::<bool>()), n as usize),
                Just(n),
            )
                .prop_map(|(rows, _)| {
                    let colors = rows.iter().map(|r| r.2).collect::<Vec<_>>();
                    let edges = rows
                        .iter()
                        .enumerate()
                        .flat_map(|(q, (a, b, _))| [(q as u32, 'a', *a), (q as u32, 'b', *b)]);
                    Builder::without_edge_colors()
                        .with_state_colors(colors)
                        .with_edges(edges)
                        .into_dfa(0)
                })
        })
    }

    /// All words over `{a, b}` up to length 5, to check languages on.
    pub fn words() -> Vec<String> {
        let mut words = vec![String::new()];
        for _ in 0..5 {
            let longer = words
                .iter()
                .flat_map(|w| [format!("{w}a"), format!("{w}b")])
                .collect::<Vec<_>>();
            words.extend(longer);
        }
        words
    }
}
