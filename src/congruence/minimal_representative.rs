use std::{cell::OnceCell, hash::Hash};

use bimap::BiBTreeMap;
use itertools::Itertools;

use crate::prelude::*;

/// Represents the minimal representative of a state in a deterministic [`TransitionSystem`], which is the length-lexicographically
/// minimal string with which the state can be reached from the [`Pointed::initial`] state.
///
/// As a transition system is equivalent to a right congruence, this type an also be seen as the minimal
/// representative of a congruence class.
#[derive(Debug, Clone)]
pub struct MinimalRepresentative<T: Deterministic>(Vec<SymbolOf<T>>, StateIndex<T>);

impl<T: Deterministic> MinimalRepresentative<T> {
    /// Returns the state index of the state that this minimal representative represents.
    pub fn state_index(&self) -> StateIndex<T> {
        self.1
    }

    pub fn decompose(self) -> (Vec<SymbolOf<T>>, StateIndex<T>) {
        (self.0, self.1)
    }
}
impl<T: Deterministic> PartialEq for MinimalRepresentative<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}
impl<T: Deterministic> PartialOrd for MinimalRepresentative<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}
impl<T: Deterministic> Ord for MinimalRepresentative<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.cmp(&other.0) {
            std::cmp::Ordering::Equal => self.1.cmp(&other.1),
            ord => ord,
        }
    }
}
impl<T: Deterministic> Eq for MinimalRepresentative<T> {}
impl<T: Deterministic> Hash for MinimalRepresentative<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<T: Deterministic> std::ops::Deref for MinimalRepresentative<T> {
    type Target = Vec<SymbolOf<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Deterministic> std::ops::DerefMut for MinimalRepresentative<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Deterministic> MinimalRepresentative<T> {
    pub fn into_inner(self) -> Vec<SymbolOf<T>> {
        self.0
    }
    pub fn new(inner: Vec<SymbolOf<T>>, id: StateIndex<T>) -> Self {
        Self(inner, id)
    }
}

impl<T: Deterministic> LinearWord<SymbolOf<T>> for MinimalRepresentative<T> {
    fn nth(&self, position: usize) -> Option<SymbolOf<T>> {
        self.0.get(position).copied()
    }
}

impl<T: Deterministic> FiniteWord<SymbolOf<T>> for MinimalRepresentative<T> {
    type Symbols<'this> = std::iter::Cloned<std::slice::Iter<'this, SymbolOf<T>>>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.0.iter().cloned()
    }
}

impl<T: Deterministic + Show> Show for MinimalRepresentative<T> {
    fn show(&self) -> String {
        if self.is_empty() {
            "ε".to_string()
        } else {
            self.0.iter().map(|sym| sym.show()).join("")
        }
    }
}

/// Gives lazy acceess to the minimal representatives of a [`RightCongruence`]. This is used
/// to avoid recomputing the minimal representatives of a congruence multiple times.
#[derive(Clone)]
pub struct LazyMinimalRepresentatives<T: Deterministic>(
    OnceCell<BiBTreeMap<StateIndex<T>, MinimalRepresentative<T>>>,
);

impl<T: Deterministic> LazyMinimalRepresentatives<T> {
    /// Tries to get access to the underlying minimal representatives. If the cache
    /// has not been initialized yet, this will return `None`.
    pub fn try_get(&self) -> Option<&BiBTreeMap<StateIndex<T>, MinimalRepresentative<T>>> {
        self.0.get()
    }

    /// Gets access to the underlying minimal representatives. If the cache has not been
    /// initialized yet, this will panic.
    pub fn get(&self) -> &BiBTreeMap<StateIndex<T>, MinimalRepresentative<T>> {
        self.0.get().expect("Cache not initialized")
    }

    /// Ensures that the minimal representatives are computed and stored in the cache.
    pub fn ensure(&self, ts: T)
    where
        T: Pointed,
    {
        self.0.get_or_init(|| {
            let mut map = BiBTreeMap::new();
            for mr in ts.minimal_representatives() {
                map.insert(mr.state_index(), mr);
            }

            map
        });
    }
}

impl<T: Deterministic> std::ops::Deref for LazyMinimalRepresentatives<T> {
    type Target = BiBTreeMap<StateIndex<T>, MinimalRepresentative<T>>;

    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

impl<T: Deterministic> Default for LazyMinimalRepresentatives<T> {
    fn default() -> Self {
        Self(OnceCell::new())
    }
}

impl<T: Deterministic> PartialEq for LazyMinimalRepresentatives<T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl<T: Deterministic> Eq for LazyMinimalRepresentatives<T> {}
