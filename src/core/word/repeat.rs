use super::{FiniteWord, Word};

/// Represents a fixed number of repetitions of a [`FiniteWord`].
#[derive(Debug, Eq, PartialEq, Hash)]
pub struct Repeat<W: FiniteWord> {
    word: W,
    times: usize,
}

impl<W: FiniteWord> Repeat<W> {
    /// Creates a new instance, repeating the word as many times as specified.
    pub fn new(word: W, times: usize) -> Self {
        Self { word, times }
    }
}

impl<W: FiniteWord> FiniteWord for Repeat<W> {
    type Symbols<'this>
        = RepeatIter<'this, W>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        RepeatIter {
            word: &self.word,
            times: self.times,
            pos: 0,
        }
    }
}

impl<W: FiniteWord> Word for Repeat<W> {
    type Symbol = W::Symbol;
    const FINITE: bool = true;

    fn nth(&self, position: usize) -> Option<W::Symbol> {
        if position < self.word.len() * self.times {
            Some(self.word.nth(position % self.word.len()).unwrap())
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct RepeatIter<'a, W: FiniteWord> {
    word: &'a W,
    times: usize,
    pos: usize,
}

impl<W: FiniteWord> Iterator for RepeatIter<'_, W> {
    type Item = W::Symbol;
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.word.len() * self.times {
            let out = self.word.nth(self.pos % self.word.len()).unwrap();
            self.pos += 1;
            Some(out)
        } else {
            None
        }
    }
}
