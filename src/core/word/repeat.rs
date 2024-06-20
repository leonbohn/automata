use std::marker::PhantomData;

use crate::prelude::Symbol;

use super::{FiniteWord, Word};

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct Repeat<S: Symbol, W: FiniteWord<S>> {
    word: W,
    times: usize,
    _pd: PhantomData<S>,
}

impl<S: Symbol, W: FiniteWord<S>> Repeat<S, W> {
    pub fn new(word: W, times: usize) -> Self {
        Self {
            word,
            times,
            _pd: PhantomData,
        }
    }
}

impl<S: Symbol, W: FiniteWord<S>> FiniteWord<S> for Repeat<S, W> {
    type Symbols<'this> = RepeatIter<'this, S, W>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        RepeatIter {
            word: &self.word,
            times: self.times,
            pos: 0,
            _pd: self._pd,
        }
    }
}

impl<S: Symbol, W: FiniteWord<S>> Word<S> for Repeat<S, W> {
    const FINITE: bool = true;

    fn nth(&self, position: usize) -> Option<S> {
        if position < self.word.len() * self.times {
            Some(self.word.nth(position % self.word.len()).unwrap())
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct RepeatIter<'a, S: Symbol, W: FiniteWord<S>> {
    word: &'a W,
    times: usize,
    _pd: PhantomData<S>,
    pos: usize,
}

impl<'a, S: Symbol, W: FiniteWord<S>> Iterator for RepeatIter<'a, S, W> {
    type Item = S;
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
