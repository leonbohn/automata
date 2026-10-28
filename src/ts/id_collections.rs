//! Containers keyed by state ids ([`IdType`]), which use dense representations (bitsets, vectors)
//! whenever the ids allow it and fall back to hash based containers otherwise.
//!
//! The representation is chosen at runtime, typically from [`crate::TransitionSystem::state_bound`].
//! Dense containers are used if a bound is known and the id type is dense, see
//! [`IdType::to_dense`].

use std::collections::{HashMap, HashSet};

use rustc_hash::FxBuildHasher;

use fixedbitset::FixedBitSet;

use super::IdType;

/// Returns true if ids of type `I` can be represented densely.
#[inline(always)]
fn is_dense_type<I: IdType>() -> bool {
    I::from_dense(0).is_some()
}

#[inline(always)]
fn dense<I: IdType>(id: I) -> usize {
    id.to_dense()
        .expect("id of a dense container must have a dense representation")
}

/// A set of state ids. Backed by a [`FixedBitSet`] if the ids are dense and a bound is known,
/// otherwise by a [`HashSet`]. A dense set grows if an id beyond the bound is inserted.
#[derive(Clone, Debug)]
pub enum StateSet<I> {
    /// Bitset indexed by [`IdType::to_dense`].
    Dense(FixedBitSet),
    /// Hash set for ids without a (known) dense bound.
    Sparse(HashSet<I, FxBuildHasher>),
}

impl<I: IdType> Default for StateSet<I> {
    fn default() -> Self {
        Self::Sparse(HashSet::default())
    }
}

impl<I: IdType> StateSet<I> {
    /// Creates an empty set. If `bound` is `Some(n)` and `I` is dense, the set is a bitset sized
    /// for the ids `0..n`, otherwise it is a hash set.
    pub fn new(bound: Option<usize>) -> Self {
        match bound {
            Some(n) if is_dense_type::<I>() => Self::Dense(FixedBitSet::with_capacity(n)),
            _ => Self::default(),
        }
    }

    /// Inserts `id`, returns true if it was not contained before.
    #[inline]
    pub fn insert(&mut self, id: I) -> bool {
        match self {
            Self::Dense(bits) => {
                let n = dense(id);
                if n >= bits.len() {
                    bits.grow(n + 1);
                }
                !bits.put(n)
            }
            Self::Sparse(set) => set.insert(id),
        }
    }

    /// Returns true if `id` is contained in the set.
    #[inline]
    pub fn contains(&self, id: &I) -> bool {
        match self {
            Self::Dense(bits) => bits.contains(dense(*id)),
            Self::Sparse(set) => set.contains(id),
        }
    }

    /// Returns the number of ids in the set.
    pub fn len(&self) -> usize {
        match self {
            Self::Dense(bits) => bits.count_ones(..),
            Self::Sparse(set) => set.len(),
        }
    }

    /// Returns true if the set is empty.
    pub fn is_empty(&self) -> bool {
        match self {
            Self::Dense(bits) => bits.is_clear(),
            Self::Sparse(set) => set.is_empty(),
        }
    }

    /// Removes all ids, keeping the allocation.
    pub fn clear(&mut self) {
        match self {
            Self::Dense(bits) => bits.clear(),
            Self::Sparse(set) => set.clear(),
        }
    }

    /// Iterates over the contained ids. Dense sets yield them in increasing order, for sparse
    /// sets the order is unspecified.
    pub fn iter(&self) -> StateSetIter<'_, I> {
        match self {
            Self::Dense(bits) => StateSetIter::Dense(bits.ones(), std::marker::PhantomData),
            Self::Sparse(set) => StateSetIter::Sparse(set.iter()),
        }
    }

    /// Returns the ids in increasing order.
    pub fn to_sorted_vec(&self) -> Vec<I> {
        let mut v: Vec<_> = self.iter().collect();
        v.sort_unstable();
        v
    }
}

/// Iterator over a [`StateSet`].
pub enum StateSetIter<'a, I> {
    #[doc(hidden)]
    Dense(fixedbitset::Ones<'a>, std::marker::PhantomData<fn() -> I>),
    #[doc(hidden)]
    Sparse(std::collections::hash_set::Iter<'a, I>),
}

impl<I: IdType> Iterator for StateSetIter<'_, I> {
    type Item = I;
    #[inline]
    fn next(&mut self) -> Option<I> {
        match self {
            Self::Dense(ones, _) => ones
                .next()
                .map(|n| I::from_dense(n).expect("bit index was produced from a valid id")),
            Self::Sparse(it) => it.next().copied(),
        }
    }
}

impl<I: IdType> Extend<I> for StateSet<I> {
    fn extend<T: IntoIterator<Item = I>>(&mut self, iter: T) {
        for id in iter {
            self.insert(id);
        }
    }
}

impl<I: IdType> FromIterator<I> for StateSet<I> {
    fn from_iter<T: IntoIterator<Item = I>>(iter: T) -> Self {
        let mut set = Self::default();
        set.extend(iter);
        set
    }
}

impl<'a, I: IdType> IntoIterator for &'a StateSet<I> {
    type Item = I;
    type IntoIter = StateSetIter<'a, I>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A map from state ids to values, see [`StateSet`] for the choice of representation.
#[derive(Clone, Debug)]
pub enum StateMap<I, V> {
    /// Vector indexed by [`IdType::to_dense`].
    Dense(Vec<Option<V>>),
    /// Hash map for ids without a (known) dense bound.
    Sparse(HashMap<I, V, FxBuildHasher>),
}

impl<I: IdType, V> Default for StateMap<I, V> {
    fn default() -> Self {
        Self::Sparse(HashMap::default())
    }
}

impl<I: IdType, V> StateMap<I, V> {
    /// Creates an empty map, which is a vector if `bound` is `Some` and `I` is dense.
    pub fn new(bound: Option<usize>) -> Self {
        match bound {
            Some(n) if is_dense_type::<I>() => {
                let mut v = Vec::new();
                v.resize_with(n, || None);
                Self::Dense(v)
            }
            _ => Self::default(),
        }
    }

    /// Inserts `value` for `id` and returns the previous value, if any.
    #[inline]
    pub fn insert(&mut self, id: I, value: V) -> Option<V> {
        match self {
            Self::Dense(v) => {
                let n = dense(id);
                if n >= v.len() {
                    v.resize_with(n + 1, || None);
                }
                v[n].replace(value)
            }
            Self::Sparse(m) => m.insert(id, value),
        }
    }

    /// Returns the value for `id`, if present.
    #[inline]
    pub fn get(&self, id: &I) -> Option<&V> {
        match self {
            Self::Dense(v) => v.get(dense(*id))?.as_ref(),
            Self::Sparse(m) => m.get(id),
        }
    }

    /// Returns a mutable reference to the value for `id`, if present.
    #[inline]
    pub fn get_mut(&mut self, id: &I) -> Option<&mut V> {
        match self {
            Self::Dense(v) => v.get_mut(dense(*id))?.as_mut(),
            Self::Sparse(m) => m.get_mut(id),
        }
    }

    /// Returns true if there is a value for `id`.
    #[inline]
    pub fn contains_key(&self, id: &I) -> bool {
        self.get(id).is_some()
    }

    /// Returns the number of entries.
    pub fn len(&self) -> usize {
        match self {
            Self::Dense(v) => v.iter().filter(|x| x.is_some()).count(),
            Self::Sparse(m) => m.len(),
        }
    }

    /// Returns true if the map has no entries.
    pub fn is_empty(&self) -> bool {
        match self {
            Self::Dense(v) => v.iter().all(Option::is_none),
            Self::Sparse(m) => m.is_empty(),
        }
    }

    /// Removes all entries, keeping the allocation.
    pub fn clear(&mut self) {
        match self {
            Self::Dense(v) => v.iter_mut().for_each(|x| *x = None),
            Self::Sparse(m) => m.clear(),
        }
    }
}

/// Assigns the ids `0..n` to the states that are inserted into it, in order of first insertion.
/// Allows to translate in both directions between state ids and a dense numbering, so that
/// algorithms can keep their bookkeeping in plain vectors.
#[derive(Clone, Debug)]
pub struct CompactIdMap<I> {
    ids: StateMap<I, usize>,
    states: Vec<I>,
}

impl<I: IdType> CompactIdMap<I> {
    /// Creates an empty map. `bound` is passed on to the underlying [`StateMap`], `capacity`
    /// is the expected number of states.
    pub fn new(bound: Option<usize>, capacity: usize) -> Self {
        Self {
            ids: StateMap::new(bound),
            states: Vec::with_capacity(capacity),
        }
    }

    /// Returns the number assigned to `state`, assigning the next free one if it has none yet.
    #[inline]
    pub fn get_or_insert(&mut self, state: I) -> usize {
        if let Some(&n) = self.ids.get(&state) {
            return n;
        }
        let n = self.states.len();
        self.states.push(state);
        self.ids.insert(state, n);
        n
    }

    /// Returns the number assigned to `state`, if any.
    #[inline]
    pub fn id(&self, state: &I) -> Option<usize> {
        self.ids.get(state).copied()
    }

    /// Returns the state that was assigned the number `n`.
    ///
    /// # Panics
    /// Panics if `n >= self.len()`.
    #[inline]
    pub fn state(&self, n: usize) -> I {
        self.states[n]
    }

    /// The states in order of their numbers.
    pub fn states(&self) -> &[I] {
        &self.states
    }

    /// The number of states that have been assigned a number.
    pub fn len(&self) -> usize {
        self.states.len()
    }

    /// Returns true if no state has been assigned a number.
    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::operations::ProductIndex;

    #[test]
    fn set_dense_and_sparse_agree() {
        let mut dense = StateSet::<u32>::new(Some(4));
        let mut sparse = StateSet::<u32>::new(None);
        assert!(matches!(dense, StateSet::Dense(_)));
        assert!(matches!(sparse, StateSet::Sparse(_)));
        for q in [3, 1, 3, 7, 0] {
            assert_eq!(dense.insert(q), sparse.insert(q));
        }
        assert_eq!(dense.len(), 4);
        assert_eq!(sparse.len(), 4);
        assert_eq!(dense.to_sorted_vec(), vec![0, 1, 3, 7]);
        assert_eq!(sparse.to_sorted_vec(), vec![0, 1, 3, 7]);
        assert!(dense.contains(&7) && !dense.contains(&2) && !dense.contains(&100));
        dense.clear();
        assert!(dense.is_empty());
    }

    #[test]
    fn non_dense_ids_use_hash_containers() {
        let mut set = StateSet::<ProductIndex<u32, u32>>::new(Some(10));
        assert!(matches!(set, StateSet::Sparse(_)));
        assert!(set.insert(ProductIndex(1, 2)));
        assert!(!set.insert(ProductIndex(1, 2)));
        assert!(matches!(
            StateMap::<ProductIndex<u32, u32>, ()>::new(Some(10)),
            StateMap::Sparse(_)
        ));
    }

    #[test]
    fn map_dense_and_sparse_agree() {
        for bound in [Some(2), None] {
            let mut m = StateMap::<u32, char>::new(bound);
            assert_eq!(m.insert(5, 'a'), None);
            assert_eq!(m.insert(5, 'b'), Some('a'));
            assert_eq!(m.get(&5), Some(&'b'));
            assert_eq!(m.get(&0), None);
            assert_eq!(m.get(&99), None);
            *m.get_mut(&5).unwrap() = 'c';
            assert!(m.contains_key(&5));
            assert_eq!(m.len(), 1);
            m.clear();
            assert!(m.is_empty());
        }
    }

    #[test]
    fn compact_ids() {
        let mut ids = CompactIdMap::<u32>::new(Some(10), 0);
        assert_eq!(ids.get_or_insert(7), 0);
        assert_eq!(ids.get_or_insert(3), 1);
        assert_eq!(ids.get_or_insert(7), 0);
        assert_eq!(ids.id(&3), Some(1));
        assert_eq!(ids.id(&4), None);
        assert_eq!(ids.state(1), 3);
        assert_eq!(ids.states(), &[7, 3]);
    }
}
