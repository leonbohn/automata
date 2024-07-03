use automata_core::{
    alphabet::{Alphabet, SimpleAlphabet},
    word::{FiniteWord, OmegaWord, Word},
};

use crate::TransitionSystem;

use super::{edge::TransitionOwnedColor, EdgeColor};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct WordTs<A: SimpleAlphabet, W: Word<Symbol = A::Symbol>, const FINITE: bool> {
    alphabet: A,
    word: W,
}

impl<A: SimpleAlphabet, W: Word<Symbol = A::Symbol>, const FINITE: bool> WordTs<A, W, FINITE> {
    pub fn new(alphabet: A, word: W) -> Self {
        Self { alphabet, word }
    }
}

impl<A: SimpleAlphabet, W: FiniteWord<Symbol = A::Symbol>> TransitionSystem
    for WordTs<A, W, false>
{
    type Alphabet = A;

    type StateIndex = u32;

    type StateColor = u32;

    type EdgeColor = A::Symbol;

    type EdgeRef<'this> = TransitionOwnedColor<'this, A::Expression, u32, EdgeColor<Self>>
    where
        Self: 'this;

    type EdgesFromIter<'this> = std::iter::Once<Self::EdgeRef<'this>>
    where
        Self: 'this;

    type StateIndices<'this> = std::ops::Range<u32>
    where
        Self: 'this;

    fn edges_from(
        &self,
        state: crate::prelude::StateIndex<Self>,
    ) -> Option<Self::EdgesFromIter<'_>> {
        if state as usize >= self.word.len() {
            return None;
        }
        let sym = self.word.nth(state as usize).unwrap();
        Some(std::iter::once(TransitionOwnedColor::new(
            state,
            self.alphabet.express(sym),
            sym,
            state + 1,
        )))
    }

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        0..(self.word.len().try_into().unwrap())
    }

    fn state_color(&self, state: crate::prelude::StateIndex<Self>) -> Option<Self::StateColor> {
        if state as usize >= self.word.len() {
            None
        } else {
            Some(state)
        }
    }
}

impl<A: SimpleAlphabet, W: OmegaWord<Symbol = A::Symbol>> TransitionSystem for WordTs<A, W, true> {
    type Alphabet = A;

    type StateIndex = u32;

    type StateColor = u32;

    type EdgeColor = A::Symbol;

    type EdgeRef<'this> = TransitionOwnedColor<'this, A::Expression, u32, EdgeColor<Self>>
    where
        Self: 'this;

    type EdgesFromIter<'this> = std::iter::Once<Self::EdgeRef<'this>>
    where
        Self: 'this;

    type StateIndices<'this> = std::ops::Range<u32>
    where
        Self: 'this;

    fn edges_from(
        &self,
        state: crate::prelude::StateIndex<Self>,
    ) -> Option<Self::EdgesFromIter<'_>> {
        if state as usize >= self.word.combined_len() {
            return None;
        }
        let sym = self.word.nth(state as usize).unwrap();

        let target = if (state + 1) as usize >= self.word.combined_len() {
            self.word.loop_index() as u32
        } else {
            state + 1
        };

        Some(std::iter::once(TransitionOwnedColor::new(
            state,
            self.alphabet.express(sym),
            sym,
            target,
        )))
    }

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        0..(self.word.combined_len().try_into().unwrap())
    }

    fn state_color(&self, state: crate::prelude::StateIndex<Self>) -> Option<Self::StateColor> {
        if state as usize >= self.word.combined_len() {
            None
        } else {
            Some(state)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;
    #[test]
    fn word_as_ts() {
        let w = WordTs::new(CharAlphabet::of_size(2), "abba");
        assert_eq!(w.state_indices_vec(), vec![0, 1, 2, 3]);
    }
}
