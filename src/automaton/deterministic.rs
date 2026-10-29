use crate::word::FiniteWord;

use crate::automaton::Automaton;
use crate::ts::{Deterministic, SymbolOf};

impl<T: Deterministic, Z> Automaton<T, Z> {
    /// Checks if two finite words are congruent in the automaton, meaning they reach the same state
    /// when starting from the initial state.
    pub fn congruent<W, V>(&self, word: W, other: V) -> bool
    where
        W: FiniteWord<Symbol = SymbolOf<T>>,
        V: FiniteWord<Symbol = SymbolOf<T>>,
    {
        self.reached_state_index(word).unwrap() == self.reached_state_index(other).unwrap()
    }
}
