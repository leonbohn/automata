use crate::core::{
    Int, Void,
    alphabet::{Alphabet, CharAlphabet},
    math::Map,
    word::FiniteWord,
};

pub type FORC<A = CharAlphabet, Q = Void, C = Void> =
    Family<RightCongruence<A>, RightCongruence<A, Q, C>>;

pub type FDFA<A = CharAlphabet> = Family<RightCongruence<A>, DFA<A>>;
pub type FWPM<A = CharAlphabet, C = Int> = Family<RightCongruence<A>, MealyMachine<A, Void, C>>;

mod fdfa;
#[allow(unused)]
pub use fdfa::*;

mod fwpm;
#[allow(unused)]
pub use fwpm::*;

mod convert;
use crate::automaton::{DFA, MealyMachine};
use crate::ts::{StateIndex, SymbolOf};
use crate::{Congruence, RightCongruence};
#[allow(unused)]
pub use convert::*;

/// Represents a family indexed by a transition system. For every
/// state/class of the leading ts, there exists an element of type `X`.
#[derive(Debug, Clone)]
pub struct Family<T: Congruence, X> {
    leading: T,
    progress: Map<StateIndex<T>, X>,
}

impl<T: Congruence, X> Family<T, X> {
    pub fn get<W>(&self, word: W) -> Option<&X>
    where
        W: FiniteWord<Symbol = SymbolOf<T>>,
    {
        self.progress.get(&self.leading.reached_state_index(word)?)
    }
    pub fn set<W>(&mut self, word: W, new_x: X) -> Option<X>
    where
        W: FiniteWord<Symbol = SymbolOf<T>>,
    {
        self.progress
            .insert(self.leading.reached_state_index(word)?, new_x)
    }
    pub fn get_mut<W>(&mut self, word: W) -> Option<&mut X>
    where
        W: FiniteWord<Symbol = SymbolOf<T>>,
    {
        self.progress
            .get_mut(&self.leading.reached_state_index(word)?)
    }
    pub(crate) fn into_parts(self) -> (T, Map<StateIndex<T>, X>) {
        (self.leading, self.progress)
    }
    pub(crate) fn from_parts(leading: T, progress: Map<StateIndex<T>, X>) -> Self {
        assert_eq!(leading.size(), progress.len());
        Self { leading, progress }
    }
    pub fn from_iter<I: IntoIterator<Item = (StateIndex<T>, X)>>(leading: T, prog_iter: I) -> Self {
        Self {
            leading,
            progress: prog_iter.into_iter().collect(),
        }
    }
}

impl<T: Congruence, X> std::ops::Index<StateIndex<T>> for Family<T, X> {
    type Output = X;
    fn index(&self, index: StateIndex<T>) -> &Self::Output {
        assert!(self.leading.contains_state_index(index));
        self.progress.get(&index).unwrap()
    }
}
impl<T: Congruence, X> std::ops::IndexMut<StateIndex<T>> for Family<T, X> {
    fn index_mut(&mut self, index: StateIndex<T>) -> &mut Self::Output {
        assert!(self.leading.contains_state_index(index));
        self.progress.get_mut(&index).unwrap()
    }
}

impl<A: Alphabet, X> Family<RightCongruence<A>, X> {
    pub fn trivial(alphabet: A, progress: X) -> Self {
        let leading = RightCongruence::new_trivial_with_initial_color(alphabet, Void, Void);
        Self::from_parts(leading, [(0, progress)].into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use automata_core::alphabet::CharAlphabet;
    #[test]
    fn family_interaction() {
        let mut fam = Family::trivial(CharAlphabet::of_size(2), 1337);
        assert_eq!(fam.get("abbabbabbabbabbaba"), Some(&1337));
        fam.set("bba", 42);
        assert_eq!(fam[0], 42);
    }
}
