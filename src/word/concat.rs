use std::hash::Hash;

use crate::prelude::AlphabetSymbol;

use super::{FiniteWord, LinearWord, OmegaWord};

/// Concatenates two words. This operation is really only sensible when the first word
/// is of finite length.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Concat<X, Y>(pub X, pub Y);

impl<S: AlphabetSymbol, X: FiniteWord<S>, Y: LinearWord<S>> LinearWord<S> for Concat<X, Y> {
    fn nth(&self, position: usize) -> Option<S> {
        if position < self.0.len() {
            self.0.nth(position)
        } else {
            self.1.nth(position - self.0.len())
        }
    }
}

impl<S: AlphabetSymbol, X: FiniteWord<S>, Y: FiniteWord<S>> FiniteWord<S> for Concat<X, Y> {
    type Symbols<'this> = std::iter::Chain<X::Symbols<'this>, Y::Symbols<'this>>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.0.symbols().chain(self.1.symbols())
    }

    fn collect_vec(&self) -> Vec<S> {
        let mut repr = self.0.collect_vec();
        repr.extend(self.1.symbols());
        repr
    }

    fn len(&self) -> usize {
        self.0.len() + self.1.len()
    }
}

impl<S: AlphabetSymbol, X: FiniteWord<S>, Y: OmegaWord<S>> OmegaWord<S> for Concat<X, Y> {
    type Spoke<'this> = Concat<&'this X, Y::Spoke<'this>>
    where
        Self: 'this;

    type Cycle<'this> = Y::Cycle<'this>
    where
        Self: 'this;

    fn spoke(&self) -> Self::Spoke<'_> {
        Concat(&self.0, self.1.spoke())
    }

    fn cycle(&self) -> Self::Cycle<'_> {
        self.1.cycle()
    }

    fn loop_index(&self) -> usize {
        self.0.len() + self.1.loop_index()
    }
}

#[cfg(test)]
mod tests {
    use crate::word::FiniteWord;

    #[test]
    fn concatenations() {
        let prefix = "abc";
        let suffix = "def";
        let combined = prefix.append(suffix);
        assert_eq!(combined.collect_vec(), vec!['a', 'b', 'c', 'd', 'e', 'f']);
    }
}
