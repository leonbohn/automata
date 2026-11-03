//! Passive and active learning of automata, moved here from the `automata-learning` crate
//! (imported by plain copy of commit `1ed4171` of its branch `phase1-baseline`).
//!
//! **Experimental:** there is no stability promise for this module until the next minor release.
// TODO(#118, phase 6): remove these once the module is documented and cleaned up
#![allow(missing_docs)]
#![allow(unused)]

/// Contains passive learners such as RPNI, DBAInf and DPAInf.
#[macro_use]
pub mod passive;

// /// Deals with active learning algorithms such as L*.
pub mod active;
mod priority_mapping;
pub use priority_mapping::{AnnotatedCongruence, Annotation, WeakPriorityMapping};

pub(crate) mod prefixtree;
