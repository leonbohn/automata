#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

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
mod show;

/// Defines a representation of directed, acyclic graphs. These are for example
/// used for the representation of the strongly connected components of a transition system.
pub mod dag;

/// Alias for the default integer type that is used for coloring edges and states.
pub type Int = u8;

/// Represents the absence of a color. The idea is that this can be used when collecting
/// a transitions system as it can always be constructed from a color by simply forgetting it.
/// This is useful for example when we want to collect a transition system into a different
/// representation, but we don't care about the colors on the edges. In that case, the state
/// colors may be kept and the edge colors are dropped.
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct Void;

impl std::fmt::Debug for Void {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#")
    }
}

/// The prelude is supposed to make using this package easier. Including everything, i.e.
/// `use automata::prelude::*;` should be enough to use the package.
pub mod prelude {
    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
    pub type TS<A = CharAlphabet, Q = Void, C = Void, const DET: bool = true> =
        LinkedListTransitionSystem<A, Q, C, DET>;
    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
    pub type DTS<A = CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, true>;
    /// Points to the default implementation of [`TransitionSystem`] in the case where it is
    /// **now known to be** [`Deterministic`].
    pub type NTS<A = CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, false>;

    #[cfg(feature = "petgraph")]
    pub use super::transition_system::impls::petgraph_backed::{petgraph, GraphTs};
    pub use super::{
        alphabet::{
            Alphabet, CharAlphabet, Expression, Matcher, PropAlphabet, PropExpression, PropSymbol,
            SimpleAlphabet, Symbol,
        },
        automaton::{
            Automaton, BuchiCondition, DeterministicOmegaAutomaton, FiniteWordAutomaton, IntoDBA,
            IntoDFA, IntoDMA, IntoDPA, IntoDRA, IntoMealyMachine, IntoMooreMachine, MealyLike,
            MealyMachine, MealySemantics, MinEvenParityCondition, MooreMachine, MooreSemantics,
            MullerCondition, NondeterministicOmegaAutomaton, OmegaAcceptanceCondition,
            OmegaAutomaton, ReachabilityCondition, Semantics, WithInitial, DBA, DFA, DMA, DPA,
        },
        congruence::{
            CollectRightCongruence, Congruence, IntoRightCongruence, MinimalRepresentative,
            RightCongruence,
        },
        dag,
        dot::Dottable,
        math,
        representation::CollectTs,
        representation::IntoTs,
        show::Show,
        transition_system::operations,
        transition_system::run::{self, InfiniteObserver, Observer, Run},
        transition_system::{
            impls::DefaultIdType,
            operations::{DefaultIfMissing, Product, ProductIndex, UniformColor},
            predecessors::PredecessorIterable,
            Deterministic, DeterministicEdgesFrom, Edge, EdgeColor, EdgeExpression, ForAlphabet,
            IndexType, IntoEdgeTuple, IsEdge, Path, ScalarIndexType, Shrinkable, Sproutable,
            StateColor, StateIndex, SymbolOf, TSBuilder, TransitionSystem,
        },
        upw, word,
        word::{
            FiniteWord, NormalizedOmegaWord, OmegaWord, PeriodicOmegaWord, ReducedOmegaWord,
            Rotate, Skip, Word,
        },
        Class, Color, Int, Pointed, Void,
    };

    pub use super::transition_system::impls::packed;
    #[cfg(feature = "implementations")]
    pub use super::transition_system::{
        EdgeLists, EdgeListsDeterministic, EdgeListsNondeterministic, LinkedListDeterministic,
        LinkedListNondeterministic, LinkedListTransitionSystem,
    };
    /// implements the interface to the `hoars` package. Is only available on create feature `hoa`.
    #[cfg(feature = "hoa")]
    pub mod hoa {
        pub use hoars::*;
    }
    #[cfg(feature = "hoa")]
    pub use crate::hoa::WriteHoa;
    use crate::transition_system::LinkedListTransitionSystem;
}

#[allow(missing_docs)]
pub mod families;

use std::{fmt::Debug, hash::Hash};

/// This module defines transition systems and successor functions and such.
#[macro_use]
pub mod transition_system;
pub use transition_system::connected_components;
pub use transition_system::{Pointed, TransitionSystem};

/// Defines automata and common types of combinations of transition system with acceptance condition.
#[allow(clippy::upper_case_acronyms)]
pub mod automaton;

/// Defines different representations of automata as mappings between an input and
/// an output alphabet.
pub mod representation;

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

/// This module deals with transforming a transition system (or similar) into a representation in the dot (graphviz) format.
pub mod dot;
pub use dot::Dottable;

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

/// Represents an ordered, finite set of colors.
pub trait Lattice {
    /// Gives an instance of the bottom, i.e. least possible color.
    fn bottom() -> Self;
    /// Gives an instance of the top, i.e. greatest possible color.
    fn top() -> Self;
    /// Joins the two colors, i.e. the least upper bound. Think of this
    /// as a union operation for sets and as maximum for numbers
    fn join(&self, other: &Self) -> Self;
    /// Joins the two colors in place. See [`Lattice::join`].
    fn join_assign(&mut self, other: &Self)
    where
        Self: Sized,
    {
        *self = self.join(other);
    }
    /// Computes the join of all colors in an iterator.
    fn join_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self
    where
        Self: 'a;
    /// Meets the two colors, i.e. the greatest lower bound. Think of this
    /// as a intersection operation for sets and as minimum for numbers
    fn meet(&self, other: &Self) -> Self;
    /// Meets the two colors in place. See [`Lattice::meet`].
    fn meet_assign(&mut self, other: &Self)
    where
        Self: Sized,
    {
        *self = self.meet(other);
    }
    /// Computes the meet of all colors in an iterator.
    fn meet_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self
    where
        Self: 'a;
}

impl Lattice for bool {
    fn bottom() -> Self {
        false
    }
    fn top() -> Self {
        true
    }
    fn join(&self, other: &Self) -> Self {
        *self || *other
    }
    fn meet(&self, other: &Self) -> Self {
        *self && *other
    }
    fn join_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self
    where
        Self: 'a,
    {
        iter.into_iter().any(|x| *x)
    }
    fn meet_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self
    where
        Self: 'a,
    {
        iter.into_iter().all(|x| *x)
    }
}

macro_rules! impl_with_limits {
    ($($ty:ident),*) => {
        $(
            impl Lattice for $ty {
                fn bottom() -> Self {  $ty::MIN }
                fn top() -> Self {  $ty::MAX }
                fn join(&self, other: &Self) -> Self {
                    std::cmp::max(*self, *other)
                }
                fn meet(&self, other: &Self) -> Self {
                    std::cmp::min(*self, *other)
                }
                fn join_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self where Self: 'a{
                    iter.into_iter().max().cloned().unwrap_or(Self::bottom())
                }
                fn meet_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self where Self: 'a{
                    iter.into_iter().min().cloned().unwrap_or(Self::top())
                }
            }
        )*
    };
}

impl_with_limits!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn lattice_ops() {
        use super::Lattice;

        assert!(true.join(&true));
        assert!(true.join(&false));
        assert!(false.join(&true));
        assert!(!false.join(&false));
        assert!(true.meet(&true));
        assert!(!true.meet(&false));
        assert!(!false.meet(&true));
        assert!(!false.meet(&false));

        assert_eq!(2.join(&7).meet(&0), 0);
    }

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
