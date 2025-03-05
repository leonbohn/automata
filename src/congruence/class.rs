use crate::core::{
    Show,
    alphabet::Symbol,
    word::{FiniteWord, Word},
};

use itertools::Itertools;

/// Represents a congruence class, which is in essence simply a non-empty sequence of symbols
/// for the underlying alphabet.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Class<S>(pub Vec<S>);

impl<S: Show> Show for Class<S> {
    fn show(&self) -> String {
        format!("[{}]", self.0.iter().map(|s| s.show()).join(""))
    }
}

impl<S> Class<S> {
    /// Creates an instance of the empty class
    pub fn epsilon() -> Self {
        Self(vec![])
    }

    /// Takes in a single symbol and returns a class containing only that symbol.
    pub fn singleton(sym: S) -> Self {
        Self(vec![sym])
    }

    /// Turns this class into a string, using the given alphabet to convert symbols to strings.
    pub fn mr_to_string(&self) -> String
    where
        S: Symbol,
    {
        if self.is_empty() {
            "ε".to_string()
        } else {
            self.0.iter().map(|sym| sym.show()).join("")
        }
    }
}

impl<S> FromIterator<S> for Class<S> {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<S: Symbol> std::fmt::Display for Class<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            if self.0.is_empty() {
                "ε".to_string()
            } else {
                self.0.iter().map(|sym| sym.show()).join("")
            }
        )
    }
}

impl<S: Symbol> Word for Class<S> {
    type Symbol = S;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<S> {
        self.0.get(position).cloned()
    }
}
impl<S: Symbol> FiniteWord for Class<S> {
    type Symbols<'this>
        = std::iter::Cloned<std::slice::Iter<'this, S>>
    where
        Self: 'this,
        S: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.0.iter().cloned()
    }

    fn collect_vec(&self) -> Vec<S> {
        self.0.clone()
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<S> std::ops::Deref for Class<S> {
    type Target = Vec<S>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<S> std::ops::DerefMut for Class<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl<S> Default for Class<S> {
    fn default() -> Self {
        Self(vec![])
    }
}
impl<S> From<Vec<S>> for Class<S> {
    fn from(value: Vec<S>) -> Self {
        Self(value)
    }
}
impl From<&str> for Class<char> {
    fn from(value: &str) -> Self {
        Self(value.chars().collect())
    }
}
impl<S: std::fmt::Debug> std::fmt::Debug for Class<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0.iter().map(|sym| format!("{:?}", sym)).join("")
        )
    }
}

impl<S: Ord> Ord for Class<S> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0
            .len()
            .cmp(&other.0.len())
            .then_with(|| self.0.cmp(&other.0))
    }
}
impl<S: Ord> PartialOrd for Class<S> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
