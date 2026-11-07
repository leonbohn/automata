//! Everything needed in typical code, so that `use automata::prelude::*;` replaces the usual
//! handful of imports.
//!
//! The prelude contains the traits whose methods are called all the time (without them in scope
//! `ts.edges_from(..)` or `dfa.accepts(..)` simply do not exist), the [`Builder`](crate::ts::Builder), the common
//! automaton aliases, the language problems and the [`upw!`](crate::upw) macro. Rarely needed or
//! specialized items (concrete adapters, observers, congruences, ...) stay in their modules.
//!
//! ```
//! use automata::prelude::*;
//!
//! let dfa = Builder::without_edge_colors()
//!     .with_state_colors([false, true])
//!     .with_transitions([(0, 'a', 1), (1, 'a', 0)])
//!     .into_dfa(0);
//! assert!(dfa.accepts("aaa"));
//! assert_eq!(dfa.state_count(), 2);
//! ```

// Alphabets and words
pub use crate::alphabet::{Alphabet, CharAlphabet};
pub use crate::upw;
pub use crate::word::{FiniteWord, OmegaWord, Word};

// Transition systems: the traits, ids, storages and the builder
pub use crate::representation::{CollectPointed, FromTransitions, IntoTransitions};
pub use crate::ts::operations::Determinize;
pub use crate::ts::{
    Builder, Deterministic, Pointed, PredecessorIterable, Sccs, Shrinkable, Sproutable, States,
    TransitionSystem, q,
};
pub use crate::ts::{StateId, StateMap, StateSet};
pub use crate::{DTS, NTS};

// Colors
pub use crate::{Color, Int, Lattice, Void};

// Automata, acceptance and the language problems
pub use crate::automaton::{
    Automaton, DBA, DCW, DFA, DMA, DPA, DRA, Disjointness, Emptiness, Equivalence, Existential,
    Inclusion, MealyMachine, MooreMachine, NBA, NCW, NFA, NMA, NPA, NRA, Semantics,
};
pub use crate::minimization::Minimize;

// Output
pub use crate::Error;
pub use crate::dot::Dottable;
#[cfg(feature = "hoa")]
pub use crate::hoa::{HoaString, WriteHoa};
