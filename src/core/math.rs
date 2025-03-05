pub use probability::{
    almost_equal, continuous_bernoulli_inverse_cumulative_density_function,
    continuous_bernoulli_mean, sample_continuous_bernoulli,
};

use std::collections::BTreeMap;
use std::{collections::BTreeSet, hash::Hash};

pub use indexmap::Equivalent;
pub use indexmap::map;
pub use indexmap::set;
pub use std::collections::btree_map as ordered_map;
pub use std::collections::btree_set as ordered_set;

/// Type alias for sets, we use this to hide which type of `HashSet` we are actually using.
pub type OrderedSet<S> = BTreeSet<S>;
/// Type alias for sets that are unordered.
pub type Set<S> = indexmap::IndexSet<S>;

/// Type alias for maps, we use this to hide which type of `HashMap` we are actually using.
pub type OrderedMap<K, V> = BTreeMap<K, V>;
/// Type alias for maps that are unordered.
pub type Map<K, V> = indexmap::IndexMap<K, V>;

/// Represents a bijective mapping between `L` and `R`, that is a mapping which associates
/// each `L` with precisely one `R` and vice versa.
pub type Bijection<L, R> = bimap::BiBTreeMap<L, R>;

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

mod probability {
    /// Computes the inverse cumulative density function of the continuous bernoulli distribution
    /// as described in [10.3390/fractalfract7050386](https://www.mdpi.com/2504-3110/7/5/386).
    pub fn continuous_bernoulli_inverse_cumulative_density_function(lambda: f64, y: f64) -> f64 {
        assert!((0.0..=1.0).contains(&lambda));
        assert!((0.0..=1.0).contains(&y));
        let fraction_numerator = (2.0 * lambda - 1.0) / (1.0 - lambda);
        let inner_numerator = 1.0 + fraction_numerator * y;
        let inner_denominator = lambda / (1.0 - lambda);
        inner_numerator.log2() / inner_denominator.log2()
    }

    /// Computes the mean of the continuous bernoulli distribution for the
    /// given parameter lambda.
    pub fn continuous_bernoulli_mean(lambda: f64) -> f64 {
        assert!((0.0..=1.0).contains(&lambda));
        let first = lambda / (2.0 * lambda - 1.0);
        let second = 1.0 / (2.0 * (1.0 - 2.0 * lambda).atanh());
        first + second
    }

    /// Samples the [continuous bernoulli distribution](https://en.wikipedia.org/wiki/Continuous_Bernoulli_distribution)
    /// by sampling a uniformly distributed value `y` between 0 and 1.
    /// The inverse of this value under the cumulative density function of the continuous
    /// bernoulli function gives a sample of this distribution.
    pub fn sample_continuous_bernoulli(lambda: f64) -> f64 {
        assert!((0.0..=1.1).contains(&lambda));
        let y = rand::random::<f64>();
        continuous_bernoulli_inverse_cumulative_density_function(lambda, y)
    }

    /// Compares two floating point numbers for equality within a certain delta.
    /// # Example
    /// ```
    /// use automata_core::math;
    ///
    /// assert!(math::almost_equal(0.7, 0.71, 0.1));
    /// assert!(!math::almost_equal(0.7, 0.91, 0.1));
    /// ```
    pub fn almost_equal(l: f64, r: f64, delta: f64) -> bool {
        l == r || ((l - r).abs() / (l.abs() + r.abs())) < delta
    }

    #[cfg(test)]
    mod tests {
        #[test]
        fn cb_test() {
            for lambda in [0.2, 0.26, 0.31, 0.37, 0.4, 0.55, 0.61, 0.7] {
                let v = (0..100000)
                    .map(|_| super::sample_continuous_bernoulli(lambda))
                    .collect::<Vec<_>>();
                let average = v.into_iter().fold(0.0, |acc, x| acc + x / 100000.0);
                let expected = super::continuous_bernoulli_mean(lambda);
                assert!(super::almost_equal(average, expected, 0.01));
            }
        }
    }
}
