use std::{cell::OnceCell, ops::Deref};

use bimap::BiBTreeMap;
use itertools::Itertools;

use crate::prelude::*;

/// Gives lazy acceess to the minimal representatives of a [`RightCongruence`]. This is used
/// to avoid recomputing the minimal representatives of a congruence multiple times.
#[derive(Debug, Clone)]
pub struct LazyMinimalRepresentatives<A: Alphabet, Idx: IndexType = usize>(
    OnceCell<BiBTreeMap<Idx, MinimalRepresentative<A::Symbol>>>,
);

impl<A: Alphabet, Idx: IndexType> LazyMinimalRepresentatives<A, Idx> {
    /// Tries to get access to the underlying minimal representatives. If the cache
    /// has not been initialized yet, this will return `None`.
    pub fn try_get(&self) -> Option<&BiBTreeMap<Idx, MinimalRepresentative<A::Symbol>>> {
        self.0.get()
    }

    /// Gets access to the underlying minimal representatives. If the cache has not been
    /// initialized yet, this will panic.
    pub fn get(&self) -> &BiBTreeMap<Idx, MinimalRepresentative<A::Symbol>> {
        self.0.get().expect("Cache not initialized")
    }

    /// Ensures that the minimal representatives are computed and stored in the cache.
    pub fn ensure<T>(&self, ts: T)
    where
        T: Congruence<Alphabet = A, StateIndex = Idx>,
    {
        self.0.get_or_init(|| {
            let mut map = BiBTreeMap::new();
            for (mr, idx) in ts.minimal_representatives() {
                map.insert(idx, MinimalRepresentative(mr));
            }

            map
        });
    }
}

impl<A: Alphabet, Idx: IndexType> Deref for LazyMinimalRepresentatives<A, Idx> {
    type Target = BiBTreeMap<Idx, MinimalRepresentative<A::Symbol>>;

    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

impl<A: Alphabet, Idx: IndexType> Default for LazyMinimalRepresentatives<A, Idx> {
    fn default() -> Self {
        Self(OnceCell::new())
    }
}

impl<A: Alphabet, Idx: IndexType> PartialEq for LazyMinimalRepresentatives<A, Idx> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl<A: Alphabet, Idx: IndexType> Eq for LazyMinimalRepresentatives<A, Idx> {}

/// Represents a minimal representative of a class in a [`RightCongruence`]. For a state
/// `q` in a congruence, the minimal representative of the class of `q` is the length-lexicographically
/// smallest word that reaches `q`/that is equivalent to `q` under the congruence.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct MinimalRepresentative<S: Symbol>(Vec<S>);

impl<S: Symbol> MinimalRepresentative<S> {
    /// Creates an instance of the empty class
    pub fn epsilon() -> Self {
        Self(vec![])
    }
}

impl<S: Symbol> LinearWord<S> for MinimalRepresentative<S> {
    fn nth(&self, position: usize) -> Option<S> {
        self.0.get(position).copied()
    }
}

impl<S: Symbol> FiniteWord<S> for MinimalRepresentative<S> {
    type Symbols<'this> = std::iter::Cloned<std::slice::Iter<'this, S>>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.0.iter().cloned()
    }
}

impl<S: Symbol + Show> Show for MinimalRepresentative<S> {
    fn show(&self) -> String {
        if self.is_empty() {
            "ε".to_string()
        } else {
            self.0.iter().map(|sym| sym.show()).join("")
        }
    }
}

impl<S: Symbol> Deref for MinimalRepresentative<S> {
    type Target = Vec<S>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<S: Symbol> FromIterator<S> for MinimalRepresentative<S> {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}
