use crate::alphabet::{Alphabet, CharAlphabet};
use crate::automaton::{DBA, DFA, DPA, MealyMachine};
use crate::learning::LearningError;
use crate::representation::CollectPointed;
use crate::ts::Deterministic;
use crate::ts::operations::Product;
use crate::{DTS, Error, Int, Pointed, TransitionSystem, Void};
use tracing::{debug, trace};

/// Contains definitions for samples, which are collections of positive and
/// negative example words.
#[macro_use]
pub mod sample;
pub use sample::{ClassOmegaSample, PeriodicOmegaSample, SetSample, SplitOmegaSample};

use crate::families::FWPM;
use crate::learning::{
    AnnotatedCongruence,
    active::{CompletingMealyOracle, LStar},
};

use self::precise::PreciseDPA;

pub use self::sample::{FiniteSample, OmegaSample};

/// Module containing the implementations of the sprout/glerc algorithm.
pub mod dpainf;

/// Defines the precise DPA.
pub mod precise;

/// Module containing the implementation of the sprout algorithm.
pub mod sprout;

/// Executes the RPNI algorithm on the given sample. This returns a DFA that is
/// composed of a right congruence as well as an acceptance condition, which marks
/// a classes as accepting if it is reached by a positive sample word.
///
/// # Errors
/// Fails if the sample is inconsistent, i.e. if no DFA with a small enough number of states can be
/// found.
///
/// # Example
/// ```
/// use automata::alphabet::CharAlphabet;
/// use automata::learning::passive::{FiniteSample, dfa_rpni};
///
/// // words with an even number of `a`
/// let word = |w: &str| w.chars().collect::<Vec<_>>();
/// let sample = FiniteSample::new_finite(
///     CharAlphabet::of_size(2),
///     [("", true), ("b", true), ("aa", true), ("baa", true), ("a", false), ("ba", false), ("aaa", false)]
///         .map(|(w, c)| (word(w), c)),
/// );
/// let dfa = dfa_rpni(&sample).unwrap();
/// for w in sample.positive_words() {
///     assert!(dfa.accepts(w));
/// }
/// for w in sample.negative_words() {
///     assert!(!dfa.accepts(w));
/// }
/// ```
pub fn dfa_rpni<A: Alphabet>(
    sample: &FiniteSample<A>,
) -> Result<DFA<DTS<A, bool, Void>>, LearningError> {
    let cong = dpainf::dpainf(sample, vec![], true, None)?;
    // the congruence is complete, so every positive word reaches a state
    let accepting = sample
        .positive_words()
        .map(|w| cong.reached_state(w).ok_or(LearningError::Incomplete))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(DFA::from_ts(cong, accepting).collect_dfa())
}

/// Executes a variant of the RPNI algorithm for omega-words, producing a DBA.
///
/// This is not implemented yet and always returns [`Error::NotYetImplemented`].
pub fn dba_rpni<A: Alphabet>(_sample: &OmegaSample<A>) -> Result<DBA<DTS<A, Void, bool>>, Error> {
    Err(Error::NotYetImplemented("dba_rpni"))
}

/// Takes a reference to an [`OmegaSample`], which classifies infinite words over the alphabet `A`
/// with boolean values and infers a [`PreciseDPA`] from it. The steps for this are roughly
/// - infer the leading prefix (aka Myhill/Nerode) congruence
/// - produce a [`SplitOmegaSample`] such that each suffix of a sample word which "starts" in a class `c`
///   gets put into the respective component of the sample for class `c`
/// - uses the glerc/sprout algorithm to infer a family of right congruences (FORC)
/// - color the FORC to obtain a canonical coloring for each class; these are then combined to an FWPM using
///   the leading congruence infered before
/// - build the precise DPA from the FWPM
///
/// # Errors
/// Fails if the sample is inconsistent or if the family needs more priorities than
/// [`precise::PRECISE_DPA_COLORS`].
///
/// # Example
/// ```
/// use automata::alphabet::CharAlphabet;
/// use automata::learning::passive::{OmegaSample, infer_precise_dpa};
/// use automata::representation::CollectPointed;
/// use automata::{Pointed, upw};
///
/// let sample = OmegaSample::new_omega_from_pos_neg(
///     CharAlphabet::of_size(3),
///     [
///         upw!("a"), upw!("aab"), upw!("aba"), upw!("aaab"), upw!("bbaa"),
///         upw!("aca"), upw!("caa"), upw!("aac"), upw!("abca"), upw!("baac"),
///     ],
///     [
///         upw!("c"), upw!("b"), upw!("bc"), upw!("abc"), upw!("acb"),
///         upw!("acc"), upw!("abb"), upw!("cba"), upw!("ac"), upw!("ba"),
///     ],
/// );
/// let dpa = infer_precise_dpa(&sample).unwrap().reachable_part().collect_dpa();
/// assert!(dpa.accepts(upw!("baa")) && !dpa.accepts(upw!("cabaca")));
/// ```
pub fn infer_precise_dpa<A: Alphabet>(
    sample: &OmegaSample<A>,
) -> Result<PreciseDPA<A, { precise::PRECISE_DPA_COLORS }>, LearningError> {
    let cong = sample.infer_prefix_congruence()?;
    let split = sample.split(&cong)?;

    let forc = split.infer_forc()?;
    trace!("{}\n{:?}", "INFERRED FORC", forc);

    let mut pms = Vec::new();
    for (class, idx) in cong.classes() {
        let periodic_sample = split
            .get(idx)
            .ok_or(LearningError::Incomplete)?
            .to_periodic_sample();
        let annotated_prc = AnnotatedCongruence::build(&forc[idx], &periodic_sample);
        trace!(
            "{} for class {:?}\t{:?}",
            "ANNOTATED CONGRUENCE", class, annotated_prc
        );
        let coloring = annotated_prc.canonic_coloring()?;
        trace!("{}{:?}", "inferred ", coloring);
        pms.push((idx, coloring));
    }
    let fwpm = FWPM::from_iter(cong.clone(), pms);
    trace!("Calculated the FWPM\n{:?}", fwpm);
    PreciseDPA::try_from(fwpm)
}

/// Similar to [`dba_rpni`], but produces a DPA instead.
///
/// # Errors
/// Fails under the same conditions as [`infer_precise_dpa`] or if L\* does not terminate.
pub fn dpa_rpni(
    sample: &OmegaSample<CharAlphabet>,
) -> Result<DPA<DTS<CharAlphabet, Void, Int>>, LearningError> {
    let precise = infer_precise_dpa(sample)?;
    let pta = sample.prefix_tree().erase_state_colors();

    let prod = precise
        .ts_product(pta)
        .map_edge_colors(|(c, _)| c)
        .erase_state_colors();

    //now we use the completed thing to learn a MealyMachine from which we can then build the DPA
    let mm = prod.reachable_part().collect_mealy();

    let alphabet = mm.alphabet().clone();
    let oracle = CompletingMealyOracle::new(mm, 0);

    let start = std::time::Instant::now();
    let learned: MealyMachine = LStar::new(alphabet, oracle).infer()?;
    debug!(
        "Learning representation of DPA with LStar took {}ms",
        start.elapsed().as_millis()
    );
    Ok(learned.collect_dpa())
}

#[cfg(test)]
mod tests {
    use crate::alphabet::CharAlphabet;
    use crate::learning::passive::{FiniteSample, dpa_rpni};
    use crate::representation::CollectPointed;
    use crate::{Pointed, States};
    use tracing::info;

    use super::OmegaSample;

    #[test]
    fn infer_precise_dpa_with_al_inf_aa() {
        let alphabet = CharAlphabet::of_size(3);
        let sample = OmegaSample::new_omega_from_pos_neg(
            alphabet,
            [
                upw!("a"),
                upw!("aab"),
                upw!("aba"),
                upw!("aaab"),
                upw!("bbaa"),
                upw!("aca"),
                upw!("caa"),
                upw!("aac"),
                upw!("abca"),
                upw!("baac"),
            ],
            [
                upw!("c"),
                upw!("b"),
                upw!("bc"),
                upw!("abc"),
                upw!("acb"),
                upw!("acc"),
                upw!("abb"),
                upw!("cba"),
                upw!("ac"),
                upw!("ba"),
            ],
        );

        let t = std::time::Instant::now();
        let dpa = super::infer_precise_dpa(&sample)
            .unwrap()
            .reachable_part()
            .collect_dpa();
        let full_duration = t.elapsed().as_millis();
        info!(
            "full construction of precise DPA size {} took {full_duration}ms",
            dpa.state_count()
        );

        let expected = [
            (upw!("cabaca"), false),
            (upw!("a"), true),
            (upw!("baa"), true),
            (upw!("baacbacbac"), true),
        ];
        for (w, c) in &expected {
            let b = dpa.accepts(w);
            assert_eq!(b, *c, "{:?} is classified {b}, expected {c}", w);
        }

        let t = std::time::Instant::now();
        let dpa_mm = dpa_rpni(&sample).unwrap();

        let paper_duration = t.elapsed().as_millis();
        info!(
            "Full construction took {full_duration}ms, paper construction took {paper_duration}ms"
        );
        assert!(dpa_mm.state_count() <= dpa.state_count());

        for (w, c) in expected {
            let b = dpa_mm.accepts(&w);
            assert_eq!(b, c, "{:?} is classified {b}, expected {c}", w);
        }
    }

    proptest::proptest! {
        #[test]
        fn dfa_rpni_is_consistent_with_the_sample(target in crate::learning::properties::dfa()) {
            let mut sample = FiniteSample::new_for_alphabet(CharAlphabet::of_size(2));
            for word in crate::learning::properties::words().iter().filter(|w| w.len() <= 4) {
                let word = word.chars().collect::<Vec<_>>();
                let accepted = target.accepts(&word);
                sample.insert(word, accepted).unwrap();
            }
            // `dfa_rpni` gives up when it needs more than `2 * max_word_len` states, which can
            // happen for a sample of a target with several states; only a result has to be right
            let learned = super::dfa_rpni(&sample);
            proptest::prop_assume!(learned.is_ok());
            let learned = learned.unwrap();
            for word in sample.positive_words() {
                proptest::prop_assert!(learned.accepts(word));
            }
            for word in sample.negative_words() {
                proptest::prop_assert!(!learned.accepts(word));
            }
        }
    }
}
