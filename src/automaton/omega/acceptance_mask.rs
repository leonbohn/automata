use bit_set::BitSet;
use itertools::Itertools;
use tracing::error;

use crate::Show;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct AcceptanceMask(BitSet);

impl AcceptanceMask {
    pub fn max(&self) -> Option<usize> {
        self.iter().max()
    }

    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter()
    }

    pub fn min(&self) -> Option<usize> {
        self.iter().min()
    }

    pub fn as_priority(&self) -> usize {
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
