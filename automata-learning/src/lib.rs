//! A library for learning automata from data.
#![allow(missing_docs)]
#![allow(unused)]

/// Contains passive learners such as RPNI, DBAInf and DPAInf.
#[macro_use]
pub mod passive;

use automata::prelude::*;

// /// Deals with active learning algorithms such as L*.
pub mod active;
mod priority_mapping;
pub use priority_mapping::{AnnotatedCongruence, Annotation, WeakPriorityMapping};

pub(crate) mod prefixtree;

mod incongruence;

#[cfg(test)]
mod tests {}
