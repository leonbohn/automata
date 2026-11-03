use std::collections::btree_map::Entry;
use std::{collections::VecDeque, io::BufRead};

use crate::alphabet::{Alphabet, CharAlphabet};
use crate::learning::LearningError;
use crate::math;
use crate::representation::CollectPointed;
use crate::ts::Deterministic;
use crate::word::{OmegaWord, PeriodicOmegaWord, ReducedOmegaWord, ReducedParseError, Word};
use crate::{Class, DTS, Pointed, RightCongruence, TransitionSystem};
use itertools::{Either, Itertools};
use thiserror::Error;
use tracing::{debug, trace};

use crate::learning::{
    passive::{
        ClassOmegaSample, SetSample,
        dpainf::{DpaInfError, dpainf, prefix_consistency_conflicts},
    },
    prefixtree::prefix_tree,
};

use super::{OmegaSample, SplitOmegaSample};

/// Abstracts the types of errors that can occur when parsing an `OmegaSample` from a string.
#[derive(Debug, Clone, Eq, PartialEq, Error)]
pub enum OmegaSampleParseError {
    /// The first line is not the header `omega`.
    #[error("missing sample header")]
    MissingHeader,
    /// The line with the alphabet is missing.
    #[error("missing sample alphabet")]
    MissingAlphabet,
    /// The line `alphabet` is not followed by `:`.
    #[error("alphabet directive not followed by `:`")]
    MissingDelimiter,
    /// A symbol of the alphabet is not a single character.
    #[error("encountered malformed alphabet symbol `{0}`")]
    MalformedAlphabetSymbol(String),
    /// A word is both positive and negative.
    #[error("sample is inconsistent: `{0}` is classified as positive and negative")]
    Inconsistent(String),
    /// The block `positive:` or `negative:` is missing.
    #[error("alphabet is malformed, missing `positive:` or `negative:` block")]
    MalformedSample,
    /// A word of the sample could not be parsed.
    #[error("could not parse given omega word, reason: {0}")]
    OmegaWordParseError(ReducedParseError),
    /// The sample could not be read.
    #[error("could not read the sample: {0}")]
    Io(String),
}

impl<A: Alphabet> OmegaSample<A> {
    /// Builds the prefix tree of all words of the sample, as a right congruence.
    pub fn prefix_tree(&self) -> RightCongruence<DTS<A>> {
        prefix_tree(self.alphabet().clone(), self.words())
            .erase_state_colors()
            .collect_right_congruence()
    }
}
impl OmegaSample<CharAlphabet> {
    /// Parses an [`OmegaSample`] from an iterator over lines, in the format described at
    /// [`Self::try_from_str`].
    pub fn try_from_lines<I: Iterator<Item = String>>(
        mut lines: I,
    ) -> Result<Self, OmegaSampleParseError> {
        if lines.next().unwrap_or_default().trim() != "omega" {
            return Err(OmegaSampleParseError::MissingHeader);
        }

        let alphabet = lines
            .next()
            .and_then(|line| {
                line.split_once(':')
                    .map(|(header, symbols)| (header.to_string(), symbols.to_string()))
            })
            .map(|(header, symbols)| {
                if header.trim() == "alphabet" {
                    symbols
                        .split(',')
                        .try_fold(Vec::new(), |mut acc, x| {
                            let sym = x.trim();
                            let mut chars = sym.chars();
                            match (chars.next(), chars.next()) {
                                (Some(c), None) => {
                                    acc.push(c);
                                    Ok(acc)
                                }
                                _ => Err(OmegaSampleParseError::MalformedAlphabetSymbol(
                                    sym.to_string(),
                                )),
                            }
                        })
                        .map(CharAlphabet::new)
                } else {
                    Err(OmegaSampleParseError::MissingAlphabet)
                }
            })
            .ok_or(OmegaSampleParseError::MissingDelimiter)??;

        if lines.next().unwrap_or_default().trim() != "positive:" {
            return Err(OmegaSampleParseError::MalformedSample);
        }

        let mut words = math::FxIndexMap::default();
        'positive: loop {
            match lines.next() {
                Some(word) => {
                    trace!("Parsing positive word \"{word}\"");
                    let word = word.trim();
                    if word.is_empty() || word.starts_with('#') || word == "negative:" {
                        break 'positive;
                    }
                    let parsed = ReducedOmegaWord::try_from_str(word)
                        .map_err(OmegaSampleParseError::OmegaWordParseError)?;
                    if let Some(_old_classification) = words.insert(parsed, true) {
                        debug!("Duplicate positive word found");
                    }
                }
                None => return Err(OmegaSampleParseError::MalformedSample),
            }
        }
        for word in lines {
            let word = word.trim();
            if word.starts_with('#') || word.is_empty() {
                continue;
            }
            trace!("Parsing negative word \"{word}\"");
            let parsed = ReducedOmegaWord::try_from_str(word)
                .map_err(OmegaSampleParseError::OmegaWordParseError)?;
            if let Some(old_classification) = words.insert(parsed, false) {
                if old_classification {
                    return Err(OmegaSampleParseError::Inconsistent(word.to_string()));
                }
                debug!("Duplicate negative word found");
            };
        }

        Ok(SetSample::new_omega(alphabet, words))
    }

    /// Parses an [`OmegaSample`] from a string. The first line is `omega`, followed by
    /// `alphabet: a,b` and the blocks `positive:` and `negative:` which contain one word per line.
    ///
    /// ```
    /// use automata::learning::passive::OmegaSample;
    ///
    /// let sample = OmegaSample::try_from_str(
    ///     "omega
    ///     alphabet: a,b
    ///     positive:
    ///     ab
    ///     negative:
    ///     b",
    /// )
    /// .unwrap();
    /// assert_eq!(sample.count_words(), 2);
    /// ```
    pub fn try_from_str(input: &str) -> Result<Self, OmegaSampleParseError> {
        Self::try_from_lines(input.lines().map(|l| l.to_string()))
    }

    /// Parses an [`OmegaSample`] from a reader, see [`Self::try_from_str`] for the format.
    /// Empty lines and lines that start with `#` are ignored.
    pub fn try_from_read<R: BufRead>(read: R) -> Result<Self, OmegaSampleParseError> {
        let mut lines = Vec::new();
        for line in read.lines() {
            let line = line
                .map_err(|e| OmegaSampleParseError::Io(e.to_string()))?
                .trim()
                .to_string();
            if !line.is_empty() && !line.starts_with('#') {
                lines.push(line);
            }
        }
        Self::try_from_lines(lines.into_iter())
    }
}

impl<A: Alphabet> OmegaSample<A> {
    /// Creates a new `OmegaSample` from an alphabet as well as two iterators, one
    /// over positive words and one over negative words.
    ///
    /// ```
    /// use automata::alphabet::CharAlphabet;
    /// use automata::learning::passive::OmegaSample;
    /// use automata::upw;
    ///
    /// let sample = OmegaSample::new_omega_from_pos_neg(
    ///     CharAlphabet::of_size(2),
    ///     [upw!("a"), upw!("ab")],
    ///     [upw!("b")],
    /// );
    /// assert_eq!((sample.count_positive_words(), sample.count_negative_words()), (2, 1));
    /// ```
    pub fn new_omega_from_pos_neg<
        W: Into<ReducedOmegaWord<A::Symbol>>,
        I: IntoIterator<Item = W>,
        J: IntoIterator<Item = W>,
    >(
        alphabet: A,
        positive: I,
        negative: J,
    ) -> Self {
        Self {
            alphabet,
            positive: positive.into_iter().map(|w| w.into()).collect(),
            negative: negative.into_iter().map(|w| w.into()).collect(),
        }
    }

    /// Returns an iterator over the positive periodic words in the sample.
    pub fn positive_periodic(&self) -> impl Iterator<Item = PeriodicOmegaWord<A::Symbol>> + '_ {
        self.positive_words()
            .filter_map(|w| PeriodicOmegaWord::try_from(w.clone()).ok())
    }

    /// Returns an iterator over the negative periodic words in the sample.
    pub fn negative_periodic(&self) -> impl Iterator<Item = PeriodicOmegaWord<A::Symbol>> + '_ {
        self.negative_words()
            .filter_map(|w| PeriodicOmegaWord::try_from(w.clone()).ok())
    }

    /// Computes a `PeriodicOmegaSample` containing only the periodic words in the sample.
    pub fn to_periodic_sample(&self) -> PeriodicOmegaSample<A> {
        PeriodicOmegaSample {
            alphabet: self.alphabet.clone(),
            positive: self.positive_periodic().collect(),
            negative: self.negative_periodic().collect(),
        }
    }

    /// Computes the [`RightCongruence`] underlying the sample.
    #[allow(clippy::result_large_err)]
    pub fn infer_prefix_congruence(&self) -> Result<RightCongruence<DTS<A>>, DpaInfError<A>> {
        dpainf(prefix_consistency_conflicts(self), vec![], true, None)
    }
}

/// A [`PeriodicOmegaSample`] is an omega sample containing only periodic words.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct PeriodicOmegaSample<A: Alphabet> {
    alphabet: A,
    positive: math::FxIndexSet<PeriodicOmegaWord<A::Symbol>>,
    negative: math::FxIndexSet<PeriodicOmegaWord<A::Symbol>>,
}

impl<A: Alphabet> PeriodicOmegaSample<A> {
    /// Gives an iterator over all positive periodic words in the sample.
    pub fn positive(&self) -> impl Iterator<Item = &PeriodicOmegaWord<A::Symbol>> + '_ {
        self.positive.iter()
    }

    /// Gives an iterator over all negative periodic words in the sample.
    pub fn negative(&self) -> impl Iterator<Item = &PeriodicOmegaWord<A::Symbol>> + '_ {
        self.negative.iter()
    }

    /// Gives the size i.e. number of positive words.
    pub fn positive_size(&self) -> usize {
        self.positive.len()
    }

    /// Gives the size i.e. number of negative words.
    pub fn negative_size(&self) -> usize {
        self.negative.len()
    }

    /// Returns the size i.e. number of words.
    pub fn size(&self) -> usize {
        self.positive_size() + self.negative_size()
    }

    /// Returns a reference to the alphabet underlying the sample.
    pub fn alphabet(&self) -> &A {
        &self.alphabet
    }

    /// Classify the given word, i.e. return `true` if it is a positive word, `false` if it is a negative word and `None` if it is neither.
    pub fn classify<W: Into<PeriodicOmegaWord<A::Symbol>>>(&self, word: W) -> Option<bool> {
        let word = word.into();
        if self.positive.contains(&word) {
            Some(true)
        } else if self.negative.contains(&word) {
            Some(false)
        } else {
            None
        }
    }

    /// Check whether the given word is contained in the sample.
    pub fn contains<W: Into<PeriodicOmegaWord<A::Symbol>>>(&self, word: W) -> bool {
        self.classify(word).is_some()
    }
}

impl<A: Alphabet> OmegaSample<A> {
    /// Create a new sample of infinite words. The words in the sample are given as an iterator yielding (word, color) pairs.
    pub fn new_omega<W: Into<ReducedOmegaWord<A::Symbol>>, J: IntoIterator<Item = (W, bool)>>(
        alphabet: A,
        words: J,
    ) -> Self {
        let (positive, negative) = words.into_iter().partition_map(|(w, b)| {
            if b {
                Either::Left(w.into())
            } else {
                Either::Right(w.into())
            }
        });

        Self {
            alphabet,
            positive,
            negative,
        }
    }

    /// Splits the sample into a map of [`ClassOmegaSample`]s, one for each class of the underlying [`RightCongruence`].
    ///
    /// # Errors
    /// Fails if the sample contains a word that is both positive and negative from some class.
    pub fn split<'a>(
        &self,
        cong: &'a RightCongruence<DTS<A>>,
    ) -> Result<SplitOmegaSample<'a, A>, LearningError> {
        let initial = cong.initial();
        // take self as is for epsilon
        let mut split = std::collections::BTreeMap::default();
        split.insert(
            initial,
            ClassOmegaSample::new(cong, Class::epsilon(), self.clone()),
        );
        let mut queue: VecDeque<_> = self
            .entries()
            .map(|(w, c)| (initial, w.reduced(), c))
            .collect();

        while let Some((state, word, color)) = queue.pop_front() {
            trace!("Processing word {:?} in state {}", word, state);
            let (sym, suffix) = word.pop_first();
            if let Some(reached) = cong.successor(state, sym) {
                trace!("\tReached successor {reached}");
                let class_sample = match split.entry(reached) {
                    Entry::Occupied(entry) => entry.into_mut(),
                    Entry::Vacant(entry) => {
                        let class = cong
                            .state_to_mr(reached)
                            .ok_or(LearningError::Incomplete)?
                            .clone()
                            .into_inner();
                        entry.insert(ClassOmegaSample::empty(
                            cong,
                            Class::from(class),
                            self.alphabet.clone(),
                        ))
                    }
                };
                if class_sample.sample_mut().insert(suffix.reduced(), color)? {
                    trace!("Added word {:?} to state {}", suffix, reached);
                    queue.push_back((reached, suffix.reduced(), color));
                }
            }
        }

        Ok(SplitOmegaSample::new(cong, split))
    }
}
