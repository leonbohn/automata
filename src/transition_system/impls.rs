#![allow(unused)]
#![allow(missing_docs)]

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord, Copy)]
pub struct Idx(usize);

impl Display for Idx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self == &Idx::sink() {
            write!(f, "⊥")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl Show for Idx {
    fn show(&self) -> String {
        self.to_string()
    }
}

impl Deref for Idx {
    type Target = usize;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Idx {
    pub fn initial() -> Self {
        Self(0)
    }
    pub fn sink() -> Self {
        Self(usize::MAX)
    }
}

impl From<usize> for Idx {
    fn from(i: usize) -> Self {
        Self(i)
    }
}

impl From<Idx> for usize {
    fn from(i: Idx) -> Self {
        i.0
    }
}

pub(crate) mod mutable_ts;
use std::{fmt::Display, ops::Deref};

pub use mutable_ts::{IntoMutableTs, MutableTs, MutableTsState};

pub(crate) mod nts;
pub use nts::{NTEdge, NTSEdgesFromIter, NTSEdgesToIter, NTSPartsFor, NTState, NTS};

pub(crate) mod dts;
pub use dts::{CollectDTS, DTSAndInitialState, DTS};

use crate::Show;
