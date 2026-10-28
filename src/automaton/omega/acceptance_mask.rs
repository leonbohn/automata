use crate::{Int, Show};

use fixedbitset::FixedBitSet;
use itertools::Itertools;
use thiserror::Error;

/// Errors concerning the acceptance sets that are attached to the edges of an omega automaton.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum AcceptanceError {
    /// An edge does not belong to any acceptance set, but exactly one is required.
    #[error("an edge has no acceptance set, but exactly one is required")]
    NoAcceptanceSet,
    /// An edge belongs to several acceptance sets, but exactly one is required.
    #[error("an edge has the acceptance sets {0:?}, but exactly one is required")]
    MultipleAcceptanceSets(Vec<Int>),
    /// The priority of an edge lies outside of the range of the acceptance condition.
    #[error("the priority {priority} is outside of the range {low}..={high} of the condition")]
    PriorityOutOfRange {
        /// The priority found on an edge.
        priority: Int,
        /// The lowest priority allowed by the condition.
        low: Int,
        /// The highest priority allowed by the condition.
        high: Int,
    },
}

/// The set of acceptance sets (numbered `0, 1, ...`) that an edge belongs to, as they are used
/// by the HOA format. Büchi conditions only use the set `0`, parity conditions require every
/// edge to belong to exactly one set, which is then interpreted as its priority.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct AcceptanceMask(FixedBitSet);

impl AcceptanceMask {
    /// Returns the largest acceptance set of the mask, or `None` if it is empty.
    pub fn max(&self) -> Option<Int> {
        self.iter().max()
    }

    /// Iterates over the acceptance sets of the mask in increasing order.
    pub fn iter(&self) -> impl Iterator<Item = Int> + '_ {
        self.0.ones().map(|x| x as Int)
    }

    /// Returns the smallest acceptance set of the mask, or `None` if it is empty.
    pub fn min(&self) -> Option<Int> {
        self.iter().min()
    }

    /// Returns the single acceptance set that the mask consists of, interpreted as a priority.
    ///
    /// # Panics
    /// Panics unless exactly one acceptance set is present, see [`Self::try_as_priority`].
    pub fn as_priority(&self) -> Int {
        self.try_as_priority()
            .expect("an edge needs exactly one acceptance set to have a priority")
    }

    /// Returns the single acceptance set that the mask consists of, interpreted as a priority.
    ///
    /// # Errors
    /// Fails with [`AcceptanceError::NoAcceptanceSet`] or
    /// [`AcceptanceError::MultipleAcceptanceSets`] unless exactly one acceptance set is present.
    pub fn try_as_priority(&self) -> Result<Int, AcceptanceError> {
        let mut it = self.iter();
        let Some(priority) = it.next() else {
            return Err(AcceptanceError::NoAcceptanceSet);
        };
        if it.next().is_some() {
            return Err(AcceptanceError::MultipleAcceptanceSets(
                self.iter().collect(),
            ));
        }
        Ok(priority)
    }

    /// Interprets the mask as a boolean for Büchi-like conditions: `false` if the edge belongs
    /// to no acceptance set and `true` otherwise (the only expected set is `0`).
    pub fn as_bool(&self) -> bool {
        let Some(next) = self.iter().next() else {
            return false;
        };
        if next != 0 {
            tracing::error!("invalid acceptance mask: {self:?}, expected color 0 or no color");
        }
        true
    }
}

impl FromIterator<Int> for AcceptanceMask {
    fn from_iter<I: IntoIterator<Item = Int>>(iter: I) -> Self {
        Self(iter.into_iter().map(|i| i as usize).collect())
    }
}

impl Show for AcceptanceMask {
    fn show(&self) -> String {
        self.iter().map(|i| format!("{{{i}}}")).join(", ")
    }
}

#[cfg(feature = "hoa")]
impl From<&hoars::AcceptanceSignature> for AcceptanceMask {
    fn from(value: &hoars::AcceptanceSignature) -> Self {
        Self(FixedBitSet::from_iter(value.iter().map(|&i| {
            i.try_into().expect("Could not cast {i} to usize")
        })))
    }
}

impl std::fmt::Debug for AcceptanceMask {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.0.ones()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{AcceptanceError, AcceptanceMask};

    #[test]
    fn priority_requires_exactly_one_acceptance_set() {
        assert_eq!(AcceptanceMask::from_iter([3]).try_as_priority(), Ok(3));
        assert_eq!(
            AcceptanceMask::from_iter([]).try_as_priority(),
            Err(AcceptanceError::NoAcceptanceSet)
        );
        assert_eq!(
            AcceptanceMask::from_iter([1, 4]).try_as_priority(),
            Err(AcceptanceError::MultipleAcceptanceSets(vec![1, 4]))
        );
    }
}
