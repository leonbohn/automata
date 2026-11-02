#![doc = include_str!("../README.md")]
//!
//! # A tour of the crate
//!
//! Data flows through four layers, and most tasks live in exactly one of them. Everything shown
//! below is available after `use automata::prelude::*;`, the other imports are spelled out.
//!
//! | Layer | Module | Central items |
//! |---|---|---|
//! | symbols | [`alphabet`] | [`Alphabet`](alphabet::Alphabet), [`CharAlphabet`](alphabet::CharAlphabet), propositional alphabets |
//! | words | [`word`] | [`FiniteWord`](word::FiniteWord), [`OmegaWord`](word::OmegaWord), [`upw!`] |
//! | transition systems | [`ts`] | [`TransitionSystem`], [`States`], [`Deterministic`], [`Sproutable`](ts::Sproutable), [`Builder`](ts::Builder) |
//! | automata | [`automaton`] | [`Automaton`], [`DFA`](automaton::DFA), [`DPA`](automaton::DPA), [`problems`](automaton::problems) |
//!
//! ## Alphabets and words
//!
//! An [`Alphabet`](alphabet::Alphabet) says which symbols exist. Edges are labeled with
//! *expressions* over the alphabet: for a simple alphabet like [`CharAlphabet`](alphabet::CharAlphabet)
//! an expression is just a symbol, for a propositional one (used by the HOA format) it is a boolean
//! formula that stands for many symbols. A *transition* is the concrete step `(state, symbol)` a
//! run takes, so one edge covers many transitions.
//!
//! Finite words are anything that implements [`FiniteWord`](word::FiniteWord) (strings, slices,
//! vectors, ...). Infinite words are in general not representable, but the ultimately periodic
//! ones `u v^ω` are, and the [`upw!`] macro writes them down. Both are fed to the same method,
//! the type of the word picks finite or omega semantics.
//!
//! ```
//! use automata::prelude::*;
//!
//! let word = upw!("ab", "c"); // a b c c c c ...
//! assert_eq!(word.spoke().len(), 2);
//! assert_eq!(word.cycle().len(), 1);
//! assert_eq!(word.nth(0), Some('a'));
//! assert_eq!(word.nth(7), Some('c'));
//! ```
//!
//! ## Transition systems
//!
//! A transition system consists of states and of edges between them, both of which can carry
//! colors. The [`TransitionSystem`] trait is the smallest interface: it can list the edges leaving
//! a state, report the color of a state and name its alphabet. Everything else is built from
//! capability traits that a system implements or not:
//!
//! | Trait | Adds |
//! |---|---|
//! | [`TransitionSystem`] | [`edges_from`](TransitionSystem::edges_from), [`state_color`](TransitionSystem::state_color), [`alphabet`](TransitionSystem::alphabet) and the lazy adapters |
//! | [`States`] | enumerating all states: [`states`](States::states), [`state_count`](States::state_count), [`quotient`](States::quotient), ... |
//! | [`Deterministic`] | exactly one successor per state and symbol: [`edge`](Deterministic::edge), [`successor`](Deterministic::successor), [`run`](Deterministic::run) |
//! | [`Pointed`] | a designated initial state, and [`reachable_part`](Pointed::reachable_part) |
//! | [`Sproutable`](ts::Sproutable) | growing: [`add_state`](ts::Sproutable::add_state), [`add_edge`](ts::Sproutable::add_edge) |
//! | [`Shrinkable`](ts::Shrinkable) | removing states and edges |
//! | [`PredecessorIterable`](ts::PredecessorIterable) | incoming edges |
//!
//! Implicit systems such as the subset construction implement only [`TransitionSystem`] (they
//! cannot list their states without exploring them). Algorithms that need all states ask for
//! [`States`], and [`Pointed::reachable_part`] turns an implicit system into one that has it.
//!
//! The easiest way to obtain a system is the [`Builder`](ts::Builder). By default it
//! produces a [`DTS`], the deterministic system over characters; [`NTS`] is the same without the
//! determinism guarantee. Use `build::<T>()` to pick any other system:
//!
//! ```
//! use automata::prelude::*;
//!
//! let dts = Builder::without_colors()
//!     .with_edges([(0, 'a', 1), (1, 'a', 0), (1, 'b', 1)])
//!     .into_dts();
//! assert_eq!(dts.state_count(), 2);
//! assert_eq!(dts.successor(q(1), 'b'), Some(q(1)));
//! assert_eq!(dts.successor(q(0), 'b'), None);
//!
//! // growing a system by hand
//! use automata::ts::ForAlphabet;
//! let mut ts = DTS::<CharAlphabet, bool, automata::Void>::for_alphabet(CharAlphabet::of_size(2));
//! let (p0, p1) = (ts.add_state(false), ts.add_state(true));
//! ts.add_edge((p0, 'a', p1));
//! assert_eq!(ts.successor(p0, 'a'), Some(p1));
//! ```
//!
//! ### Storage
//!
//! Systems that own their states and edges are *storages*. They differ in how they trade
//! generality for speed:
//!
//! | Storage | Marker | Use it for |
//! |---|---|---|
//! | [`LinkedTs`](ts::LinkedTs) | [`Linked`](ts::Linked) | the default; any alphabet, nondeterminism, cheap growth and removal (removed items leave tombstones so [`EdgeId`](ts::EdgeId)s stay valid, [`compact`](ts::LinkedTs::compact) renumbers) |
//! | [`Det<T>`](ts::Det) | [`Det<Linked>`](ts::Det) | wraps another storage and makes determinism part of the type; adding an edge replaces overlapping ones. [`DTS`] is `Det<LinkedTs<..>>` |
//! | [`DenseTs`](ts::DenseTs) | [`Dense`](ts::Dense) | deterministic, one slot per state and symbol, the fastest lookups, needs a small indexed alphabet |
//! | [`CsrTs`](ts::CsrTs) | [`Csr`](ts::Csr) | immutable compressed rows, built in one go from another system, the most compact |
//!
//! The marker types let code be generic over the representation, for example a parser that is
//! instantiated with [`Linked`](ts::Linked) or `Det<Linked>`.
//!
//! ### Adapters and `collect`
//!
//! Operations that change a system ([`map_edge_colors`](TransitionSystem::map_edge_colors),
//! [`with_state_color`](TransitionSystem::with_state_color),
//! [`restrict_state_indices`](TransitionSystem::restrict_state_indices), products, quotients,
//! reversal, the subset construction, ...) do not copy anything. Each returns a lazy view that
//! computes its result on every query and memoizes nothing. Chain as many as needed, then
//! materialize the result once with `collect`:
//!
//! ```
//! use automata::prelude::*;
//! use automata::ts::DenseTs;
//!
//! let ts = Builder::without_colors()
//!     .with_edges([(0, 'a', 1), (1, 'a', 0), (1, 'b', 1), (0, 'b', 0)])
//!     .into_dts();
//!
//! // nothing is computed here ...
//! let view = (&ts).map_edge_colors(|_| true);
//! // ... until we collect into a storage of our choice
//! let dense: DenseTs<_, automata::Void, bool> = view.collect();
//! assert_eq!(dense.state_count(), 2);
//! assert_eq!(dense.successor(q(0), 'a'), Some(q(1)));
//! ```
//!
//! Collecting is the generic conversion between systems: [`IntoTransitions`](representation::IntoTransitions) and
//! [`FromTransitions`](representation::FromTransitions) are the `IntoIterator` and `FromIterator` of transition systems. The
//! adapters of a [`Pointed`] system keep the initial state, and `collect_dfa`, `collect_dpa`, ...
//! from [`CollectPointed`](representation::CollectPointed) directly produce an automaton.
//!
//! Other bridges are the [`Determinize`](ts::operations::Determinize) problem, which turns a
//! nondeterministic system into a deterministic one with the subset construction, and the
//! traversals [`Bfs`](ts::Bfs), [`Dfs`](ts::Dfs) and the strongly connected components
//! [`Sccs`](ts::Sccs).
//!
//! ## Automata and acceptance
//!
//! An [`Automaton<T, Sem>`](Automaton) pairs a transition system `T` with an initial state and a
//! [`Semantics`](automaton::Semantics) `Sem` that decides which words are accepted. There is
//! nothing to remember about acceptance beyond the aliases:
//!
//! | Alias | Words | Colors | Accepts if |
//! |---|---|---|---|
//! | [`DFA`](automaton::DFA) | finite | state: `bool` | the reached state is accepting |
//! | [`MooreMachine`](automaton::MooreMachine), [`MealyMachine`](automaton::MealyMachine) | finite | state / edge | (computes an output) |
//! | [`DBA`](automaton::DBA) | infinite | edge: `bool` | an accepting edge is seen infinitely often |
//! | [`DPA`](automaton::DPA) | infinite | edge: `Int` | the least priority seen infinitely often is even |
//! | [`DRA`](automaton::DRA), [`DMA`](automaton::DMA) | infinite | edge | Rabin / Muller condition on the infinity set |
//!
//! For omega automata acceptance looks at the *edges* taken infinitely often. The word
//! passed to [`accepts`](Automaton::accepts) selects the semantics:
//!
//! ```
//! use automata::prelude::*;
//!
//! let dpa = Builder::without_state_colors()
//!     .with_transitions([(0, 'a', 0, 0), (0, 'b', 1, 0)])
//!     .into_dpa(0);
//! assert!(dpa.accepts(upw!("b", "a")));   // edge priority 0 repeats
//! assert!(!dpa.accepts(upw!("a", "b")));  // only priority 1 repeats
//! ```
//!
//! Automata that arrive from the outside with a condition only known at runtime (the HOA parser)
//! use [`OmegaAcceptanceCondition`](automaton::OmegaAcceptanceCondition).
//!
//! ## Operations and problems
//!
//! Boolean operations ([`union`](automaton::DFA::union), [`intersection`](automaton::DFA::intersection),
//! [`negation`](automaton::DFA::negation), [`DPA::complement`](automaton::DPA)) and
//! [`minimization`](minimization::Minimize) work on automata directly. Questions about languages
//! are phrased as *problems*: a value that states the question, with methods that answer it and
//! (where there is one) produce a witness.
//!
//! | Problem | Question | Methods |
//! |---|---|---|
//! | [`Emptiness::of(&a)`](automaton::Emptiness) | is `L(a)` empty? | `holds`, `witness` |
//! | [`Inclusion::of(&a).within(&b)`](automaton::Inclusion) | `L(a) ⊆ L(b)`? | `holds`, `counterexample` |
//! | [`Equivalence::of(&a).and(&b)`](automaton::Equivalence) | `L(a) = L(b)`? | `holds`, `counterexample` |
//! | [`Disjointness::of(&a).and(&b)`](automaton::Disjointness) | `L(a) ∩ L(b) = ∅`? (DFAs) | `holds` |
//! | [`Minimize::on(&m)`](minimization::Minimize) | the minimal machine | `run` |
//! | [`Determinize::on(&ts)`](ts::operations::Determinize) | subset construction | `run` |
//!
//! ```
//! use automata::prelude::*;
//!
//! let even_as = Builder::without_edge_colors()
//!     .with_state_colors([true, false])
//!     .with_transitions([(0, 'a', 1), (1, 'a', 0), (0, 'b', 0), (1, 'b', 1)])
//!     .into_dfa(0);
//! let odd_as = even_as.negation();
//!
//! assert!(Disjointness::of(&even_as).and(&odd_as).holds());
//! assert!(!Equivalence::of(&even_as).and(&odd_as).holds());
//! let cex = Equivalence::of(&even_as).and(&odd_as).counterexample();
//! assert!(cex.is_some());
//! assert!(Inclusion::of(&even_as).within(&even_as).holds());
//! ```
//!
//! Language problems on omega automata expect complete automata: a word without a run is ignored.
//!
//! ## Errors and panics
//!
//! Library code does not panic on input; fallible operations return a typed error that converts
//! into the crate-wide [`Error`]. Panics that remain are programmer errors (for example an empty
//! cycle in a periodic word) and are documented in a `# Panics` section.
//!
//! ## Input and output
//!
//! Every system and automaton can be written as DOT with [`Dottable`](dot::Dottable) (images need the
//! `render` or `graphviz` feature). With the default feature `hoa`, deterministic Büchi and parity
//! automata are read and written in the HOA format, see the `hoa` module.
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

/// The crate-wide [`Error`] type.
pub mod error;
pub use error::Error;

/// An alphabet defines a collection of possible symbols. This
/// module implements simple alphabets which consist of just a
/// collection of symbols, and propositional alphabets where each
/// symbol is represented by a boolean expression over some
/// set of base atomic propositions.
#[macro_use]
pub mod alphabet;

/// A word is a sequence of symbols from some alphabet. Herein,
/// different types of words are defined, specifically finite ones
/// and different reprsentations of infinite ones.
/// Moreover, some constructions of manipulating words, taking suffixes,
/// infixes and such are given.
/// Finally, the module also implements normalization for words.
#[macro_use]
pub mod word;

/// Defines some mathematical objects that are used such as bijections,
/// sets and mappings.
pub mod math;

/// Partitions of a set into classes, e.g. induced by a congruence.
pub mod partition;

/// Defines a representation of directed, acyclic graphs. These are for example
/// used for the representation of the strongly connected components of a transition system.
pub mod dag;

mod color;
mod table;
pub use color::{Color, Int, Lattice, Void};

/// The default deterministic transition system: a [`ts::LinkedTs`] wrapped in [`ts::Det`], which
/// replaces overlapping edges when an edge is added.
pub type DTS<A = alphabet::CharAlphabet, Q = Void, C = Void> = ts::Det<ts::LinkedTs<A, Q, C>>;
/// The default transition system for systems that are **not known to be** [`Deterministic`]: a
/// [`ts::LinkedTs`].
pub type NTS<A = alphabet::CharAlphabet, Q = Void, C = Void> = ts::LinkedTs<A, Q, C>;

#[cfg(feature = "hoa")]
pub mod hoa;

/// Families of objects that are indexed by the classes of a right congruence, for example
/// families of DFAs (`FDFA`) or of weak priority mappings (`FWPM`), and conversions between them.
/// Needs the feature `families`.
#[cfg(feature = "families")]
pub mod families;

/// This module defines transition systems and successor functions and such.
#[macro_use]
pub mod ts;
pub use ts::{Deterministic, Pointed, States, TransitionSystem};

/// Defines automata and common types of combinations of transition system with acceptance condition.
#[allow(clippy::upper_case_acronyms)]
pub mod automaton;
pub use automaton::Automaton;

/// Defines different representations of automata as mappings between an input and
/// an output alphabet.
pub mod representation;

/// Defines congruence relations and congruence classes.
pub mod congruence;
pub use congruence::{Class, Congruence, RightCongruence};

pub mod minimization;

/// Everything needed in typical code: `use automata::prelude::*;`.
pub mod prelude;

/// Implements the generation of random transition systems.
#[cfg(feature = "random")]
pub mod random;

pub mod dot;

#[cfg(test)]
mod tests {
    use crate::{DTS, Void};

    pub fn wiki_dfa() -> crate::automaton::DFA<DTS<crate::alphabet::CharAlphabet, bool, Void>> {
        use crate::ts::Builder;

        Builder::without_edge_colors()
            .with_state_colors([false, false, true, true, true, false])
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 2),
                (1, 'a', 0),
                (1, 'b', 3),
                (2, 'a', 4),
                (2, 'b', 5),
                (3, 'a', 4),
                (3, 'b', 5),
                (4, 'a', 4),
                (4, 'b', 5),
                (5, 'a', 5),
                (5, 'b', 5),
            ])
            .into_dfa(0)
    }
}
