use std::{cell::OnceCell, hash::Hash};

use crate::core::{
    Show, math,
    word::{FiniteWord, Word},
};
use crate::ts::{StateIndex, SymbolOf};
use crate::{Pointed, TransitionSystem};
use bimap::BiBTreeMap;
use itertools::Itertools;

/// Represents a bijection between state indices of a transition
/// system and the minimal representative word.
pub struct StateNaming<T: TransitionSystem>(math::Bijection<StateIndex<T>, Vec<SymbolOf<T>>>);

impl<T: TransitionSystem> FromIterator<(StateIndex<T>, Vec<SymbolOf<T>>)> for StateNaming<T> {
    fn from_iter<I: IntoIterator<Item = (StateIndex<T>, Vec<SymbolOf<T>>)>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}
impl<T: TransitionSystem> FromIterator<MinimalRepresentative<T>> for StateNaming<T> {
    fn from_iter<I: IntoIterator<Item = MinimalRepresentative<T>>>(iter: I) -> Self {
        Self(
            iter.into_iter()
                .map(MinimalRepresentative::into_name)
                .collect(),
        )
    }
}

impl<T: TransitionSystem> std::ops::Deref for StateNaming<T> {
    type Target = math::Bijection<StateIndex<T>, Vec<SymbolOf<T>>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<T: TransitionSystem> std::ops::DerefMut for StateNaming<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Represents the minimal representative of a state in a deterministic [`TransitionSystem`], which is the length-lexicographically
/// minimal string with which the state can be reached from the [`Pointed::initial`] state.
///
/// As a transition system is equivalent to a right congruence, this type an also be seen as the minimal
/// representative of a congruence class.
#[derive(Debug, Clone)]
pub struct MinimalRepresentative<T: TransitionSystem>(Vec<SymbolOf<T>>, StateIndex<T>);

impl<T: TransitionSystem> MinimalRepresentative<T> {
    /// Returns the state index of the state that this minimal representative represents.
    pub fn state_index(&self) -> StateIndex<T> {
        self.1
    }

    /// Turns the minimal representative into a state name, which is a pair
    /// consisting of the state's index and a `Vec` representing the minimal
    /// representative (i.e. length-lexicographically minimal string on which
    /// the state is reached).
    pub fn into_name(self) -> (StateIndex<T>, Vec<SymbolOf<T>>) {
        (self.1, self.0)
    }

    /// Decomposes `self` into its inner vector of symbols and the state index.
    pub fn decompose(self) -> (Vec<SymbolOf<T>>, StateIndex<T>) {
        (self.0, self.1)
    }
    /// Consumes `self` and returns the inner vector of symbols.
    pub fn into_inner(self) -> Vec<SymbolOf<T>> {
        self.0
    }
    /// Creates a new instance of `MinimalRepresentative` from the given inner vector of symbols and state index.
    pub fn new(inner: Vec<SymbolOf<T>>, id: StateIndex<T>) -> Self {
        Self(inner, id)
    }
}
impl<T: TransitionSystem> PartialEq for MinimalRepresentative<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}
impl<T: TransitionSystem> PartialOrd for MinimalRepresentative<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<T: TransitionSystem> Ord for MinimalRepresentative<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.cmp(&other.0) {
            std::cmp::Ordering::Equal => self.1.cmp(&other.1),
            ord => ord,
        }
    }
}
impl<T: TransitionSystem> Eq for MinimalRepresentative<T> {}
impl<T: TransitionSystem> Hash for MinimalRepresentative<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<T: TransitionSystem> std::ops::Deref for MinimalRepresentative<T> {
    type Target = Vec<SymbolOf<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: TransitionSystem> std::ops::DerefMut for MinimalRepresentative<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: TransitionSystem> Word for MinimalRepresentative<T> {
    type Symbol = SymbolOf<T>;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<SymbolOf<T>> {
        self.0.get(position).copied()
    }
}

impl<T: TransitionSystem> FiniteWord for MinimalRepresentative<T> {
    type Symbols<'this>
        = std::iter::Cloned<std::slice::Iter<'this, SymbolOf<T>>>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.0.iter().cloned()
    }
}

impl<T: TransitionSystem + Show> Show for MinimalRepresentative<T> {
    fn show(&self) -> String {
        if self.is_empty() {
            "ε".to_string()
        } else {
            self.0.iter().map(|sym| sym.show()).join("")
        }
    }
}

/// Gives lazy acceess to the minimal representatives of a [`crate::RightCongruence`]. This is used
/// to avoid recomputing the minimal representatives of a congruence multiple times.
#[derive(Clone, Debug)]
pub struct LazyMinimalRepresentatives<T: TransitionSystem>(
    OnceCell<BiBTreeMap<StateIndex<T>, MinimalRepresentative<T>>>,
);

impl<T: TransitionSystem> LazyMinimalRepresentatives<T> {
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
    pub fn ensure(&self, ts: &T) -> &BiBTreeMap<StateIndex<T>, MinimalRepresentative<T>>
    where
        T: Pointed,
    {
        self.ensure_from(ts, ts.initial())
    }

    /// Ensures that the minimal representatives are computed and stored in the cache, and
    /// considering `intitial` as the starting state.
    pub fn ensure_from(
        &self,
        ts: &T,
        initial: StateIndex<T>,
    ) -> &BiBTreeMap<StateIndex<T>, MinimalRepresentative<T>> {
        self.0.get_or_init(|| {
            let mut map = BiBTreeMap::new();
            for mr in ts.minimal_representatives_iter_from(initial) {
                map.insert(mr.state_index(), mr);
            }

            map
        });
        self.get()
    }
}

impl<T: TransitionSystem> std::ops::Deref for LazyMinimalRepresentatives<T> {
    type Target = BiBTreeMap<StateIndex<T>, MinimalRepresentative<T>>;

    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

impl<T: TransitionSystem> Default for LazyMinimalRepresentatives<T> {
    fn default() -> Self {
        Self(OnceCell::new())
    }
}

impl<T: TransitionSystem> PartialEq for LazyMinimalRepresentatives<T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl<T: TransitionSystem> Eq for LazyMinimalRepresentatives<T> {}
