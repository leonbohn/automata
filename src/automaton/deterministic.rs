use crate::core::{Color, alphabet::Alphabet, word::FiniteWord};

use crate::Pointed;
use crate::automaton::Automaton;
use crate::ts::Deterministic;

impl<A, Z, Q, C, D, const OMEGA: bool> Automaton<A, Z, Q, C, D, OMEGA, true>
where
    A: Alphabet,
    D: Deterministic<Alphabet = A, StateColor = Q, EdgeColor = C> + Pointed,
    Q: Color,
    C: Color,
{
    /// Checks if two finite words are congruent in the automaton, meaning they reach the same state
    /// when starting from the initial state.
    pub fn congruent<W, V>(&self, word: W, other: V) -> bool
    where
        W: FiniteWord<Symbol = A::Symbol>,
        V: FiniteWord<Symbol = A::Symbol>,
    {
        self.reached_state_index(word).unwrap() == self.reached_state_index(other).unwrap()
    }
}
