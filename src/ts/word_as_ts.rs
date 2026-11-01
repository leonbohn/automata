use std::borrow::Cow;

use crate::TransitionSystem;
use crate::alphabet::SimpleAlphabet;
use crate::ts::{EdgeOf, StateIndex, States, predecessors::PredecessorIterable};
use crate::word::{Finite, FiniteWord, Omega, OmegaWord, Word};

use super::EdgeRef;

/// Treats a word as if it was a transition system.
///
/// For a finite word, this is equivalent to a transition system that is a chain. The last edge
/// leads to the state `word.len()`, which does not belong to the system.
///
/// For an infinite word, this is a transition system consisting of a spoke and
/// an attached loop.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct WordTs<A: SimpleAlphabet, W: Word<Symbol = A::Symbol>> {
    alphabet: A,
    word: W,
}

/// The shape of the system that a kind of word ([`Finite`] or [`Omega`]) is read as. This lets
/// [`WordTs`] have the same implementations for finite and infinite words.
pub trait WordKind<W> {
    /// The number of states, i.e. the number of positions of `word` that are stored.
    fn len(word: &W) -> usize;
    /// The state that the last edge leads back to, `None` if the word does not loop.
    fn loop_start(word: &W) -> Option<usize>;
}

impl<W: FiniteWord> WordKind<W> for Finite {
    fn len(word: &W) -> usize {
        word.len()
    }

    fn loop_start(_word: &W) -> Option<usize> {
        None
    }
}

impl<W: OmegaWord> WordKind<W> for Omega {
    fn len(word: &W) -> usize {
        word.combined_len()
    }

    fn loop_start(word: &W) -> Option<usize> {
        Some(word.loop_index())
    }
}

impl<A: SimpleAlphabet, W: Word<Symbol = A::Symbol>> WordTs<A, W> {
    /// Creates a new instance from a given alphabet and a word.
    pub fn new(alphabet: A, word: W) -> Self {
        Self { alphabet, word }
    }
}

impl<A: SimpleAlphabet, W: Word<Symbol = A::Symbol>> WordTs<A, W>
where
    W::Kind: WordKind<W>,
{
    fn len(&self) -> usize {
        <W::Kind as WordKind<W>>::len(&self.word)
    }

    /// The edge that reads position `source` of the word and leads to `target`.
    fn edge(&self, source: u32, target: u32) -> Option<EdgeOf<'_, Self>> {
        let sym = self.word.nth(source as usize)?;
        Some(EdgeRef::owned(
            source,
            self.alphabet.express(sym),
            sym,
            target,
        ))
    }
}

impl<A: SimpleAlphabet, W: Word<Symbol = A::Symbol>> TransitionSystem for WordTs<A, W>
where
    W::Kind: WordKind<W>,
{
    type Alphabet = A;

    type StateIndex = u32;

    type StateColor = u32;

    type EdgeColor = A::Symbol;

    type EdgesFromIter<'this>
        = std::option::IntoIter<EdgeOf<'this, Self>>
    where
        Self: 'this;

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        let len = self.len();
        if state as usize >= len {
            return None;
        }
        let target = if (state as usize) + 1 < len {
            state + 1
        } else {
            <W::Kind as WordKind<W>>::loop_start(&self.word).map_or(state + 1, |l| l as u32)
        };
        Some(self.edge(state, target).into_iter())
    }

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        ((state as usize) < self.len()).then_some(Cow::Owned(state))
    }
}

impl<A: SimpleAlphabet, W: Word<Symbol = A::Symbol>> States for WordTs<A, W>
where
    W::Kind: WordKind<W>,
{
    type StatesIter<'this>
        = std::ops::Range<u32>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        0..u32::try_from(self.len()).unwrap_or(u32::MAX)
    }

    fn state_count(&self) -> usize {
        self.len()
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        (index as usize) < self.len()
    }
}

impl<A: SimpleAlphabet, W: Word<Symbol = A::Symbol>> PredecessorIterable for WordTs<A, W>
where
    W::Kind: WordKind<W>,
{
    type EdgesToIter<'this>
        = std::iter::Chain<
        std::option::IntoIter<EdgeOf<'this, Self>>,
        std::option::IntoIter<EdgeOf<'this, Self>>,
    >
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        let len = self.len();
        if state as usize >= len {
            return None;
        }
        let previous = state.checked_sub(1).and_then(|p| self.edge(p, state));
        let closing = <W::Kind as WordKind<W>>::loop_start(&self.word)
            .filter(|l| *l == state as usize)
            .and_then(|_| self.edge(len as u32 - 1, state));
        Some(previous.into_iter().chain(closing))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alphabet::CharAlphabet;

    #[test]
    fn finite_word_is_a_chain() {
        let w = WordTs::new(CharAlphabet::of_size(2), "abba");
        assert_eq!(w.states().collect::<Vec<_>>(), vec![0, 1, 2, 3]);
        assert_eq!(w.predecessors(0).unwrap().count(), 0);
        assert_eq!(w.predecessors(3).unwrap().count(), 1);
        assert!(w.predecessors(4).is_none());
    }

    #[test]
    fn omega_word_loops_back() {
        let w = WordTs::new(CharAlphabet::of_size(2), upw!("a", "ab"));
        assert_eq!(w.state_count(), 3);
        let last = w.edges_from(2).unwrap().next().unwrap();
        assert_eq!(last.target(), 1);
        assert_eq!(w.predecessors(1).unwrap().count(), 2);
        assert_eq!(w.predecessors(2).unwrap().count(), 1);
    }

    #[test]
    fn periodic_word_closes_at_the_first_state() {
        let w = WordTs::new(CharAlphabet::of_size(2), upw!("ab"));
        assert_eq!(w.predecessors(0).unwrap().count(), 1);
    }
}
