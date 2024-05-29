#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

/// The prelude is supposed to make using this package easier. Including everything, i.e.
/// `use automata::prelude::*;` should be enough to use the package.
pub mod prelude {
    pub use automata_core::{
        alphabet, alphabet::Alphabet, alphabet::CharAlphabet, alphabet::Expression,
        alphabet::Matcher, alphabet::Symbol, math, Color, IdType, Int, ScalarIdType, Show, Void,
    };

    #[cfg(not(feature = "petgraph"))]
    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
    pub type TS<A = CharAlphabet, Q = Void, C = Void, const DET: bool = true> =
        LinkedListTransitionSystem<A, Q, C, DET>;
    #[cfg(feature = "petgraph")]
    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
    pub type TS<A = CharAlphabet, Q = Void, C = Void, const DET: bool = true> =
        GraphTs<A, Q, C, DET>;
    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
    pub type DTS<A = CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, true>;
    /// Points to the default implementation of [`TransitionSystem`] in the case where it is
    /// **now known to be** [`Deterministic`].
    pub type NTS<A = CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, false>;

    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case which
    /// is mutable. Especially, this type implements [`Shrinkable`] and [`Sproutable`], which allows
    /// removing and adding transitions.
    pub type MutableTs<A = CharAlphabet, Q = Void, C = Void> = EdgeLists<A, Q, C>;
    /// The nondeterministic variant of [`MutableTs`].
    pub type MutableTsNondeterministic<A = CharAlphabet, Q = Void, C = Void> =
        EdgeListsNondeterministic<A, Q, C>;

    #[cfg(feature = "petgraph")]
    pub use super::transition_system::impls::pg::{node_index, petgraph, state_index, GraphTs};

    pub use super::{
        automaton::{
            Automaton, BuchiCondition, DeterministicOmegaAutomaton, FiniteSemantics,
            FiniteWordAutomaton, IntoDBA, IntoDFA, IntoDMA, IntoDPA, IntoDRA, IntoMealyMachine,
            IntoMooreMachine, MealyMachine, MealySemantics, MinEvenParityCondition, MooreMachine,
            MooreSemantics, MullerCondition, NondeterministicOmegaAutomaton,
            OmegaAcceptanceCondition, OmegaAutomaton, OmegaSemantics, ReachabilityCondition,
            Semantics, WithInitial, DBA, DFA, DMA, DPA,
        },
        congruence::{
            CollectRightCongruence, Congruence, IntoRightCongruence, MinimalRepresentative,
            RightCongruence,
        },
        transition_system::operations,
        transition_system::{
            dot::Dottable,
            impls::DefaultIdType,
            operations::{DefaultIfMissing, Product, ProductIndex, UniformColor},
            predecessors::PredecessorIterable,
            run::{FiniteRun, OmegaRun},
            Deterministic, DeterministicEdgesFrom, Edge, EdgeColor, EdgeExpression, EdgeLists,
            EdgeListsDeterministic, EdgeListsNondeterministic, EdgeReference, EdgeTuple,
            ForAlphabet, Id, IntoEdgeTuple, IsEdge, LinkedListDeterministic,
            LinkedListNondeterministic, LinkedListTransitionSystem, Path, Shrinkable, Sproutable,
            StateColor, StateIndex, SymbolOf, TSBuilder, TransitionSystem,
        },
        upw,
        word::{
            FiniteWord, LinearWord, NormalizedOmegaWord, OmegaWord, PeriodicOmegaWord,
            ReducedOmegaWord, ReducedParseError,
        },
        Class, Pointed,
    };
}

/// Reexports mathematical objects for things like sets, maps and bijections.
pub mod math {
    pub use automata_core::math::*;
}

/// This module defines transition systems and successor functions and such.
#[macro_use]
pub mod transition_system;
pub use transition_system::connected_components;
pub use transition_system::{Pointed, TransitionSystem};

/// Defines automata and common types of combinations of transition system with acceptance condition.
#[allow(clippy::upper_case_acronyms)]
pub mod automaton;

/// Defines congruence relations and congruence classes.
pub mod congruence;
pub use congruence::{Class, Congruence, RightCongruence};

/// Module that contains definitions for dealing with words.
#[macro_use]
pub mod word;

/// Contains implementations different minimization algorithms. This is feature gated behind the `minimize` feature.
#[cfg(feature = "minimize")]
pub mod minimization;

#[cfg(feature = "hoa")]
pub mod hoa;

/// Implements the generation of random transition systems.
#[cfg(feature = "random")]
pub mod random;

/// Implements a directed acyclic graph.
pub mod dag;

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    pub fn wiki_dfa() -> DFA<CharAlphabet> {
        TSBuilder::without_edge_colors()
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
