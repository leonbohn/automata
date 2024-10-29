use crate::core::{Int, Show};

use bit_set::BitSet;
use itertools::Itertools;
use tracing::error;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct AcceptanceMask(BitSet);

impl AcceptanceMask {
    pub fn max(&self) -> Option<Int> {
        self.iter().max()
    }

    pub fn iter(&self) -> impl Iterator<Item = Int> + '_ {
        self.0.iter().map(|x| x as Int)
    }

    pub fn min(&self) -> Option<Int> {
        self.iter().min()
    }

    pub fn as_priority(&self) -> Int {
        let mut it = self.iter();
        let Some(priority) = it.next() else {
            error!(
                "no priority is set on the edge, we require each edge to have precisely one color"
            );
            panic!("could not extract priority from acceptance mask");
        };
        if it.next().is_some() {
            error!(
                "more than one priority is set on the edge: {:?}, but we require edges to have precisely one color",
                self.0
            );
            panic!("could not extract priority from acceptance mask");
        }
        priority
    }

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

impl Show for AcceptanceMask {
    fn show(&self) -> String {
        self.iter().map(|i| format!("{{{i}}}")).join(", ")
    }
}

impl From<&hoars::AcceptanceSignature> for AcceptanceMask {
    fn from(value: &hoars::AcceptanceSignature) -> Self {
        Self(BitSet::from_iter(value.iter().map(|&i| {
            i.try_into().expect("Could not cast {i} to usize")
        })))
    }
}

impl std::fmt::Debug for AcceptanceMask {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}
