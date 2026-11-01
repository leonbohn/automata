use thiserror::Error;

use super::{FiniteWord, Word};

/// Returned when trying to construct a [`NonEmpty`] word from an empty one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
#[error("the word is empty")]
pub struct EmptyWordError;

/// A finite word that is guaranteed to contain at least one symbol.
///
/// # Example
/// ```
/// use automata::word::{EmptyWordError, NonEmpty};
///
/// assert!(NonEmpty::new("ab").is_ok());
/// assert_eq!(NonEmpty::new(""), Err(EmptyWordError));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NonEmpty<W>(pub(super) W);

impl<W: FiniteWord> NonEmpty<W> {
    /// Wraps `word`, failing if it is empty.
    pub fn new(word: W) -> Result<Self, EmptyWordError> {
        if word.is_empty() {
            Err(EmptyWordError)
        } else {
            Ok(Self(word))
        }
    }

    /// Gives a reference to the wrapped word.
    pub fn as_inner(&self) -> &W {
        &self.0
    }

    /// Unwraps the underlying word.
    pub fn into_inner(self) -> W {
        self.0
    }
}

impl<W: FiniteWord> Word for NonEmpty<W> {
    type Symbol = W::Symbol;
    type Kind = super::Finite;
    fn nth(&self, position: usize) -> Option<W::Symbol> {
        self.0.nth(position)
    }
}

impl<W: FiniteWord> FiniteWord for NonEmpty<W> {
    type Symbols<'this>
        = W::Symbols<'this>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.0.symbols()
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}
