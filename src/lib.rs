#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

/// The prelude is supposed to make using this package easier. Including everything, i.e.
/// `use automata::prelude::*;` should be enough to use the package.
pub mod prelude {
    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
    pub type TS<A = CharAlphabet, Q = Void, C = Void, const DET: bool = true> =
        GraphTs<A, Q, C, DET>;
    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
    pub type DTS<A = CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, true>;
    /// Points to the default implementation of [`TransitionSystem`] in the case where it is
    /// **now known to be** [`Deterministic`].
    pub type NTS<A = CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, false>;

    pub use super::transition_system::impls::pg::{petgraph, GraphTs};
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
            Deterministic, DeterministicEdgesFrom, Edge, EdgeColor, EdgeExpression, ForAlphabet,
            IndexType, IntoEdgeTuple, IsEdge, Path, ScalarIndexType, Shrinkable, Sproutable,
            StateColor, StateIndex, SymbolOf, TSBuilder, TransitionSystem,
        },
        Class, Color, Pointed,
    };
    pub use automata_core::prelude::*;

    #[cfg(feature = "implementations")]
    pub use super::transition_system::{
        EdgeLists, EdgeListsDeterministic, EdgeListsNondeterministic, LinkedListDeterministic,
        LinkedListNondeterministic, LinkedListTransitionSystem,
    };
}

pub use automata_core::math;

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

/// Contains implementations different minimization algorithms.
pub mod minimization;

#[cfg(feature = "hoa")]
pub mod hoa;

/// Implements the generation of random transition systems.
#[cfg(feature = "random")]
pub mod random;

/// Implements a directed acyclic graph.
pub mod dag;

use std::{fmt::Debug, hash::Hash};

/// A color is simply a type that can be used to color states or transitions.
pub trait Color: Clone + Eq + Hash + Debug {
    /// Reduces a sequence of colors (of type `Self`) to a single color of type `Self`.
    fn reduce<I: IntoIterator<Item = Self>>(iter: I) -> Self
    where
        Self: Sized + Ord,
    {
        iter.into_iter().min().unwrap()
    }
}

impl<T: Eq + Clone + Hash + Debug> Color for T {}

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
