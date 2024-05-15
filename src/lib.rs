#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

/// The prelude is supposed to make using this package easier. Including everything, i.e.
/// `use automata::prelude::*;` should be enough to use the package.
pub mod prelude {
    pub use super::{
        alphabet,
        alphabet::{CharAlphabet, Expression, Symbol},
        automaton::{
            Automaton, DBASemantics, DFASemantics, FiniteSemantics, IntoDBA, IntoDFA, IntoDPA,
            IntoMealyMachine, IntoMooreMachine, MealyMachine, MealySemantics,
            MinEvenParitySemantics, MooreMachine, MooreSemantics, OmegaAcceptanceCondition,
            OmegaAutomaton, OmegaSemantics, Semantics, WithInitial, DBA, DFA, DPA,
        },
        congruence::{Congruence, RightCongruence},
        math,
        transition_system::operations,
        transition_system::{
            dot::Dottable,
            operations::{Product, ProductIndex},
            predecessors::PredecessorIterable,
            reachable::MinimalRepresentative,
            run::{FiniteRun, OmegaRun},
            Deterministic, DeterministicEdgesFrom, Edge, EdgeColor, ExpressionOf, ForAlphabet,
            IndexType, Indexes, IntoEdge, IsEdge, MutableTs, Path, Sproutable, StateColor,
            SymbolOf, TSBuilder, TransitionSystem, DTS, NTS,
        },
        upw,
        word::{
            FiniteWord, LinearWord, NormalizedOmegaWord, OmegaWord, PeriodicOmegaWord,
            ReducedOmegaWord, ReducedParseError,
        },
        Alphabet, Class, Color, Pointed, Show, Void,
    };
}

/// This module contains some definitions of mathematical objects which are used throughout the crate and
/// do not really fit to the top level.
pub mod math;

/// Module that contains definitions for dealing with alphabets.
pub mod alphabet;
pub use alphabet::Alphabet;
use itertools::Itertools;

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
pub use congruence::{Class, RightCongruence};

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

use std::{fmt::Debug, hash::Hash};

/// A color is simply a type that can be used to color states or transitions.
pub trait Color: Clone + Eq + Ord + Hash + Show {
    /// Reduces a sequence of colors (of type `Self`) to a single color of type `Self`.
    fn reduce<I: IntoIterator<Item = Self>>(iter: I) -> Self
    where
        Self: Sized,
    {
        iter.into_iter().min().unwrap()
    }
}

impl<T: Eq + Ord + Clone + Hash + Show> Color for T {}

/// Represents the absence of a color. The idea is that this can be used when collecting
/// a transitions system as it can always be constructed from a color by simply forgetting it.
/// This is useful for example when we want to collect a transition system into a different
/// representation, but we don't care about the colors on the edges. In that case, the state
/// colors may be kept and the edge colors are dropped.
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct Void;

impl<C: Color> From<C> for Void {
    fn from(_: C) -> Self {
        Void
    }
}

impl Debug for Void {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#")
    }
}

impl<C: Show> Show for (C, Void) {
    fn show(&self) -> String {
        self.0.show()
    }
}

impl<C: Show> Show for (Void, C) {
    fn show(&self) -> String {
        self.1.show()
    }
}

impl Show for (Void, Void) {
    fn show(&self) -> String {
        "-".to_string()
    }
}
impl<C: Show> Show for (C, &Void) {
    fn show(&self) -> String {
        self.0.show()
    }
}

impl<C: Show> Show for (&Void, C) {
    fn show(&self) -> String {
        self.1.show()
    }
}

impl Show for (&Void, &Void) {
    fn show(&self) -> String {
        "-".to_string()
    }
}

/// Helper trait which can be used to display states, transitions and such.
pub trait Show {
    /// Returns a human readable representation of `self`, for a state index that should be
    /// for example q0, q1, q2, ... and for a transition (q0, a, q1) it should be (q0, a, q1).
    /// Just use something that makes sense. This is mainly used for debugging purposes.
    fn show(&self) -> String;
    /// Show a collection of the thing, for a collection of states this should be {q0, q1, q2, ...}
    /// and for a collection of transitions it should be {(q0, a, q1), (q1, b, q2), ...}.
    /// By default this is unimplemented.
    fn show_collection<'a, I>(_iter: I) -> String
    where
        Self: 'a,
        I: IntoIterator<Item = &'a Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        unimplemented!("This operation makes no sense.")
    }
}

impl Show for Option<usize> {
    fn show(&self) -> String {
        match self {
            None => "".to_string(),
            Some(x) => x.show(),
        }
    }

    fn show_collection<'a, I>(iter: I) -> String
    where
        Self: 'a,
        I: IntoIterator<Item = &'a Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        usize::show_collection(iter.into_iter().filter_map(|x| x.as_ref()))
    }
}

impl Show for usize {
    fn show(&self) -> String {
        self.to_string()
    }
    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        format!(
            "[{}]",
            itertools::Itertools::join(&mut iter.into_iter().map(|x| x.show()), ", ")
        )
    }
}
impl Show for String {
    fn show(&self) -> String {
        self.clone()
    }
}

impl Show for () {
    fn show(&self) -> String {
        "-".into()
    }
    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(_iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        "-".to_string()
    }
}

impl<S: Show> Show for [S] {
    fn show(&self) -> String {
        format!(
            "\"{}\"",
            itertools::Itertools::join(&mut self.iter().map(|x| x.show()), "")
        )
    }

    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        format!(
            "{{{}}}",
            itertools::Itertools::join(&mut iter.into_iter().map(|x| x.show()), ", ")
        )
    }
}

impl<S: Show> Show for Vec<S> {
    fn show(&self) -> String {
        S::show_collection(self.iter())
    }
}

impl<S: Show, T: Show> Show for (S, T) {
    fn show(&self) -> String {
        format!("({}, {})", self.0.show(), self.1.show())
    }
}

impl Show for bool {
    fn show(&self) -> String {
        match self {
            true => "+",
            false => "-",
        }
        .to_string()
    }

    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        format!("{{{}}}", iter.into_iter().map(Show::show).join(", "))
    }
}

impl<S: Show> Show for &S {
    fn show(&self) -> String {
        S::show(*self)
    }
}

/// Type alias for sets, we use this to hide which type of `HashSet` we are actually using.
pub type Set<S> = fxhash::FxHashSet<S>;
/// Type alias for maps, we use this to hide which type of `HashMap` we are actually using.
pub type Map<K, V> = fxhash::FxHashMap<K, V>;

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
