use super::FiniteSample;
use crate::alphabet::Alphabet;
use itertools::Itertools;
use thiserror::Error;

/// The errors that can occur when parsing a finite sample. There are none yet, as parsing is not
/// implemented.
#[derive(Debug, Clone, Error)]
pub enum FiniteSampleParseError {}

impl<A: Alphabet> FiniteSample<A> {
    /// Create a new sample of finite words from the given alphabet and iterator over annotated words. The sample is given
    /// as an iterator over its symbols. The words are given as an iterator of pairs (word, color).
    ///
    /// ```
    /// use automata::alphabet::CharAlphabet;
    /// use automata::learning::passive::FiniteSample;
    ///
    /// let sample = FiniteSample::new_finite(
    ///     CharAlphabet::of_size(2),
    ///     [(vec!['a', 'b'], true), (vec!['b'], false)],
    /// );
    /// assert_eq!(sample.count_words(), 2);
    /// ```
    pub fn new_finite<I: IntoIterator<Item = A::Symbol>, J: IntoIterator<Item = (I, bool)>>(
        alphabet: A,
        words: J,
    ) -> Self {
        let (positive, negative) = words.into_iter().partition_map(|(w, c)| {
            if c {
                itertools::Either::Left(w.into_iter().collect())
            } else {
                itertools::Either::Right(w.into_iter().collect())
            }
        });
        Self {
            alphabet,
            positive,
            negative,
        }
    }

    /// Returns the maximum length of any finite word in the sample. Gives back `0` if no word exists in the sample.
    pub fn max_word_len(&self) -> usize {
        self.words().map(|w| w.len()).max().unwrap_or(0)
    }
}
