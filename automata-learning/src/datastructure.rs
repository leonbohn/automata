use std::{
    cmp::Ordering,
    fmt::Debug,
    ops::{Deref, DerefMut},
};

use automata::prelude::{Show, Symbol};

mod discrimination_tree;
mod incongruence;

#[derive(Clone, Eq, PartialEq)]
pub struct Factor<S>(Vec<S>);

impl<S> Factor<S> {
    pub fn without_last(&self) -> Option<Self>
    where
        S: Clone,
    {
        if self.is_empty() {
            return None;
        }
        Some(Self(self.0[..self.len() - 1].to_vec()))
    }
}

impl<S> Deref for Factor<S> {
    type Target = Vec<S>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<S> DerefMut for Factor<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<S> FromIterator<S> for Factor<S> {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<S: Show> std::fmt::Debug for Factor<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for sym in self.0.iter().map(|sym| sym.show()) {
            f.write_str(&sym)?;
        }
        Ok(())
    }
}

impl<S: Ord> Ord for Factor<S> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.len().cmp(&other.0.len()).then(
            self.0
                .iter()
                .zip(other.0.iter())
                .find_map(|(l, r)| {
                    let ord = l.cmp(r);
                    if ord != Ordering::Equal {
                        Some(ord)
                    } else {
                        None
                    }
                })
                .unwrap_or(Ordering::Equal),
        )
    }
}
impl<S: Ord> PartialOrd for Factor<S> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
