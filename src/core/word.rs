use std::hash::Hash;

use crate::alphabet::Symbol;

mod skip;
pub use skip::Skip;

mod concat;
pub use concat::Concat;

mod normalized;
pub use normalized::NormalizedOmegaWord;

mod finite;
pub use finite::FiniteWord;

mod omega;
pub use omega::{OmegaWord, PeriodicOmegaWord, ReducedOmegaWord, ReducedParseError};

mod repeat;
pub use repeat::Repeat;

mod rotate;
pub use rotate::Rotate;

pub use self::skip::Infix;

/// A linear word is a word that can be indexed by a `usize`. This is the case for both finite and
/// infinite words.
pub trait Word: Hash + Eq {
    /// Represents the type of symbol making up the word.
    type Symbol: Symbol;

    /// Constant that indicates whether the word is finite or not.
    const FINITE: bool;

    /// Returns the symbol at the given `position` in `self`, if it exists.
    fn nth(&self, position: usize) -> Option<Self::Symbol>;

    /// Returns the first symbol of `self`, if it exists.
    fn first(&self) -> Option<Self::Symbol>
    where
        Self: Sized,
    {
        self.nth(0)
    }

    /// Builds an infix of `self` by starting at the given `offset` and taking the given `length`.
    ///
    /// # Example
    /// ```
    /// use automata_core::word::{Word, FiniteWord};
    /// let word = "abcde".to_string();
    /// assert_eq!(word.infix(1, 3).as_string(), "bcd");
    /// ```
    fn infix(&self, offset: usize, length: usize) -> Infix<'_, Self>
    where
        Self: Sized,
    {
        Infix::new(self, offset, length)
    }

    /// Constructs an [`Infix`] object, which is a finite prefix of `self` that has the given `length`.
    fn prefix(&self, length: usize) -> Infix<'_, Self>
    where
        Self: Sized,
    {
        Infix::new(self, 0, length)
    }

    /// Removes the first symbol of `self` and returns it together with the remaining suffix.
    fn pop_first(&self) -> (Self::Symbol, skip::Skip<'_, Self>)
    where
        Self: Sized,
    {
        let first = self.first().unwrap();
        (first, self.skip(1))
    }

    /// Creates an [`crate::word::Skip`] object, which is the suffix of `self` that starts at the given `offset`.
    fn skip(&self, offset: usize) -> skip::Skip<'_, Self>
    where
        Self: Sized,
    {
        skip::Skip::new(self, offset)
    }
}

impl<W: Word + ?Sized> Word for &W {
    type Symbol = W::Symbol;
    const FINITE: bool = W::FINITE;
    fn nth(&self, position: usize) -> Option<W::Symbol> {
        W::nth(self, position)
    }
}

/// A type of iterator for infixes of [`Word`]s. It is actually consumed by iteration.
///
/// Stores a reference to the iterated word as well as a start and end position. When `next` is called,
/// we check if the start position is strictly smaller than the end position, and if so, we return the symbol at
/// the start position and increment it. Otherwise, we return `None`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ConsumingInfixIterator<'a, W: Word> {
    word: &'a W,
    start: usize,
    end: usize,
}

impl<W: Word> Word for ConsumingInfixIterator<'_, W> {
    type Symbol = W::Symbol;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<W::Symbol> {
        self.word.nth(self.start + position)
    }
}

impl<W: Word> Iterator for ConsumingInfixIterator<'_, W> {
    type Item = W::Symbol;
    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let out = self.word.nth(self.start);
            self.start += 1;
            out
        } else {
            None
        }
    }
}

impl<'a, W: Word> ConsumingInfixIterator<'a, W> {
    /// Creates a new [`ConsumingInfixIterator`] object from a reference to a word and a start and end position.
    pub fn new(word: &'a W, start: usize, end: usize) -> Self {
        Self { word, start, end }
    }
}

/// This macro can be used to create a [`ReducedOmegaWord`] object from some representation, it is mainly interesting
/// for quickly constructing infinite words without having to go through the [`ReducedOmegaWord`] struct.
///
/// There are essentially two distinct variants of using this macro:
/// - `upw!(base, recur)` creates an ultimately word with the representation of `base` followed by the representation of `recur`.
/// - `upw!(recur)` creates a periodic word that is the repetition of `recur`.
///
/// # Example:
/// ```
/// use automata_core::{upw, word::{FiniteWord, OmegaWord}};
///
/// let ultimately_periodic = upw!("ab", "bb"); // represents the ultimately periodic word `ab(bb)^𝜔`
/// assert!(ultimately_periodic.spoke().finite_word_equals("a")); // the spoke is normalized to just `a`
/// assert!(ultimately_periodic.cycle().finite_word_equals("b")); // while the loop normalizes to `b`
///
/// let periodic_word = upw!("bbbbb"); // we can also create a periodic omega word
/// assert!(periodic_word.spoke().is_empty()); // which is normlalized to have an empty spoke
/// assert!(periodic_word.cycle().finite_word_equals("b")); // and a cycle that equals the omega iteration of `b`.
/// ```
#[macro_export]
macro_rules! upw {
    ($recur:expr) => {
        $crate::word::ReducedOmegaWord::periodic($recur)
    };
    ($base:expr, $recur:expr) => {
        $crate::word::ReducedOmegaWord::ultimately_periodic($base, $recur)
    };
}

#[cfg(test)]
mod tests {
    use crate::word::{FiniteWord, Word};

    #[test]
    fn macro_upw() {
        let w = upw!("a", "bbbb");
        let ww = upw!("ab", "b");
        assert_eq!(w.prefix(6).collect_vec(), ww.prefix(6).collect_vec());
    }

    #[test]
    fn bug_upw() {
        let first = upw!("baa", "ba");
        assert_eq!(first, upw!("ba", "ab"));
        let second = upw!("bab", "ab");
        assert_eq!(second, upw!("ba"));
    }
}
