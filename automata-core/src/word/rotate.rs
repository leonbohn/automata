use std::ops::Rem;

use crate::alphabet::Symbol;

use super::{FiniteWord, OmegaWord, PeriodicOmegaWord, Word};

/// Implementors of this trait can be rotated in either direction, i.e.
/// to the left or to the right. This is mainly interesting for the
/// looping part of an ultimately periodic omega-word.
pub trait Rotate: Word {
    /// Rotates the word left by the given number of symbols. For example
    /// calling the method for the word "asdf" with 2 should result in
    /// the word "dfas".
    ///
    /// This should never panic if the number is too large, instead calling
    /// with 6 on "asdf" should return the same as calling with 2.
    fn rotate_left(&mut self, number: usize);
    /// Clones `self` and then calls [`Self::rotate_left`] on the clone.
    fn cloned_rotate_left(&self, number: usize) -> Self
    where
        Self: Clone,
    {
        let mut out = self.clone();
        out.rotate_left(number);
        out
    }

    /// Rotates `self` right by the given number of symbols. This
    /// method should not panic if the number is greater than the
    /// word's length. See [`Self::rotate_left`] for more details.
    fn rotate_right(&mut self, number: usize);

    /// Clones the word and rotates right by the given number of symbols
    /// by calling [`Self::rotate_right`] on the clone.
    fn cloned_rotate_right(&self, number: usize) -> Self
    where
        Self: Clone,
    {
        let mut out = self.clone();
        out.rotate_right(number);
        out
    }

    /// Returns an iterator over the rotations of the word.
    ///
    /// For example, the rotations of the word "asdf" would be
    /// "asdf", "sdfa", "dfas", "fasd".
    fn rotations(&self) -> Rotations<Self::Symbol>;
}

impl<S: Symbol> Rotate for PeriodicOmegaWord<S> {
    fn rotate_left(&mut self, number: usize) {
        let mid = number.rem(number);
        self.representation_mut().rotate_left(mid)
    }
    fn rotate_right(&mut self, number: usize) {
        let mid = number.rem(number);
        self.representation_mut().rotate_right(mid)
    }
    fn rotations(&self) -> Rotations<S> {
        Rotations {
            repr: self.cycle_vec().repeat(2).into_vec(),
            start: 0,
            len: self.cycle_len(),
        }
    }
}

pub struct Rotations<S> {
    repr: Vec<S>,
    start: usize,
    len: usize,
}

impl<S: Symbol> Iterator for Rotations<S> {
    type Item = Vec<S>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.start + self.len < self.repr.len() {
            let out = self.repr[self.start..(self.start + self.len)].to_vec();
            self.start += 1;
            Some(out)
        } else {
            None
        }
    }
}
