use std::{collections::BTreeSet, hash::Hash};

/// A partition is a different view on a congruence relation, by grouping elements of
/// type `I` into their respective classes under the relation.
#[derive(Debug, Clone)]
pub struct Partition<I: Hash + Eq>(Vec<BTreeSet<I>>);

impl<I: Hash + Eq> std::ops::Deref for Partition<I> {
    type Target = Vec<BTreeSet<I>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, I: Hash + Eq> IntoIterator for &'a Partition<I> {
    type Item = &'a BTreeSet<I>;
    type IntoIter = std::slice::Iter<'a, BTreeSet<I>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<I: Hash + Eq> PartialEq for Partition<I> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().all(|o| other.contains(o))
    }
}
impl<I: Hash + Eq> Eq for Partition<I> {}

impl<I: Hash + Eq + Ord> Partition<I> {
    /// Returns the size of the partition, i.e. the number of classes.
    pub fn size(&self) -> usize {
        self.0.len()
    }

    /// Builds a new congruence relation from an iterator that yields iterators
    /// which yield elements of type `I`.
    pub fn new<X: IntoIterator<Item = I>, Y: IntoIterator<Item = X>>(iter: Y) -> Self {
        Self(
            iter.into_iter()
                .map(|it| it.into_iter().collect::<BTreeSet<_>>())
                .collect(),
        )
    }
}

impl<I: Hash + Eq + Ord> From<Vec<BTreeSet<I>>> for Partition<I> {
    fn from(value: Vec<BTreeSet<I>>) -> Self {
        Self(value)
    }
}
