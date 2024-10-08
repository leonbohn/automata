use std::ops::Rem;

use crate::prelude::Symbol;

use super::{FiniteWord, OmegaWord, PeriodicOmegaWord, Word};

pub trait Rotate: Word {
    fn rotate_left(&mut self, number: usize);
    fn cloned_rotate_left(&self, number: usize) -> Self
    where
        Self: Clone,
    {
        let mut out = self.clone();
        out.rotate_left(number);
        out
    }

    fn rotate_right(&mut self, number: usize);
    fn cloned_rotate_right(&self, number: usize) -> Self
    where
        Self: Clone,
    {
        let mut out = self.clone();
        out.rotate_right(number);
        out
    }

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
