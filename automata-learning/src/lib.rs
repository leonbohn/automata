//! A library for learning automata from data.
#![allow(missing_docs)]
#![allow(unused)]

/// Contains passive learners such as RPNI, DBAInf and DPAInf.
#[macro_use]
pub mod passive;

use automata::prelude::*;

// /// Deals with active learning algorithms such as L*.
pub mod active;
pub mod prefixtree;

pub mod observable;

#[cfg(test)]
mod tests {}
