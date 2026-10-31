use crate::word::FiniteWord;

use crate::automaton::Automaton;
use crate::ts::{Deterministic, SymbolOf};

impl<T: Deterministic, Sem> Automaton<T, Sem> {
    /// Checks if two finite words are congruent in the automaton, meaning they reach the same state
    /// when starting from the initial state.
    ///
    /// Returns `None` if one of the words has no run from the initial state, which can happen if
    /// the transition system is not complete.
    pub fn congruent<W, V>(&self, word: W, other: V) -> Option<bool>
    where
        W: FiniteWord<Symbol = SymbolOf<T>>,
        V: FiniteWord<Symbol = SymbolOf<T>>,
    {
        Some(self.reached_state(word)? == self.reached_state(other)?)
    }
}
