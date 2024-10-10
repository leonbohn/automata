use crate::prelude::*;
use math::Map;

/// Represents a family indexed by a transition system. For every
/// state/class of the leading ts, there exists an element of type `X`.
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

impl<T: Congruence, X> Family<T, X> {
    pub fn from(leading: T, progress: Map<StateIndex<T>, X>) -> Self {
        Self { leading, progress }
    }
}

impl<A: Alphabet, X> Family<RightCongruence<A>, X> {
    pub fn trivial(alphabet: A, progress: X) -> Self {
        let leading = RightCongruence::new_trivial_with_initial_color(alphabet, Void, Void);
        Self::from(leading, [(0, progress)].into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn family_interaction() {
        let mut fam = Family::trivial(CharAlphabet::of_size(2), 1337);
        assert_eq!(fam.get("abbabbabbabbabbaba"), Some(&1337));
        fam.set("bba", 42);
        assert_eq!(fam[0], 42);
    }
}
