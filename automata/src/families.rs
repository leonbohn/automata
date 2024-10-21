use crate::prelude::*;
use math::Map;

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
        Self::builder()
            .with_leading(leading)
            .with_progress_from_iter(progress)
            .construct()
    }
    pub fn from_iter<I: IntoIterator<Item = (StateIndex<T>, X)>>(leading: T, prog_iter: I) -> Self {
        Self::builder()
            .with_leading(leading)
            .with_progress_from_iter(prog_iter)
            .construct()
    }
    pub fn for_leading(leading: T) -> FamilyBuilder<T, X> {
        FamilyBuilder::create().with_leading(leading)
    }
    pub fn builder() -> FamilyBuilder<T, X> {
        FamilyBuilder::create()
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

#[allow(unused)]
#[allow(missing_docs)]
mod builder {
    use std::fmt::Debug;

    use super::*;
    use indexmap::map::MutableKeys;
    use thiserror::Error;

    #[derive(Clone, Copy, Eq, Error, PartialEq, Debug)]
    pub enum FamilyBuilderError<Idx: IndexType = DefaultIdType> {
        #[error("Missing congruence")]
        MissingCongruence,
        #[error("Incomplete progress: missing for state {0:?}")]
        MissingProgess(Idx),
        #[error("Surplus progress: progress for state {0:?} is not needed")]
        SurplusProgress(Idx),
    }

    #[derive(Debug, Clone)]
    pub struct FamilyBuilder<T: Congruence, X> {
        cong: Option<T>,
        progress: Map<StateIndex<T>, X>,
    }

    impl<T: Congruence, X> FamilyBuilder<T, X> {
        pub fn construct(self) -> Family<T, X> {
            match self.try_construct() {
                Ok(fam) => fam,
                Err(e) => panic!("Failed to construct family: {:?}", e),
            }
        }

        pub fn try_construct(self) -> Result<Family<T, X>, FamilyBuilderError<StateIndex<T>>> {
            let Some(cong) = self.cong else {
                return Err(FamilyBuilderError::MissingCongruence);
            };

            for state in cong.state_indices() {
                if !self.progress.contains_key(&state) {
                    return Err(FamilyBuilderError::MissingProgess(state));
                }
            }
            if cong.size() != self.progress.len() {
                let mut set = self.progress;
                set.retain(|q, _| cong.contains_state_index(*q));
                let surplus = set.first().expect("Must exist!").0;
                return Err(FamilyBuilderError::SurplusProgress(*surplus));
            }

            Ok(Family::from_parts(cong, self.progress))
        }

        pub fn with_leading(mut self, cong: T) -> Self {
            self.cong = Some(cong);
            self
        }

        pub fn with_progress(mut self, state: &StateIndex<T>, x: X) -> Self {
            self.progress.insert(*state, x);
            self
        }

        pub fn with_progress_from_iter(
            mut self,
            progress: impl IntoIterator<Item = (StateIndex<T>, X)>,
        ) -> Self {
            self.progress = progress.into_iter().collect();
            self
        }

        pub fn create() -> Self {
            Self {
                cong: None,
                progress: Map::new(),
            }
        }
    }
}
pub use builder::FamilyBuilder;

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
