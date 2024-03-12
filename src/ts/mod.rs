use crate::{Class, Color, Map, RightCongruence, Show, Void};
use std::fmt::Display;

/// Contains the most central trait for this module, the trait [`TransitionSystem`].
#[macro_use]
pub mod transition_system;

pub use transition_system::{DeterministicEdgesFrom, ExpressionOf, SymbolOf, TransitionSystem};

/// Defines implementations for common operations on automata/transition systems.
pub mod operations;

mod index_ts;
pub use index_ts::{HashTs, IntoHashTs};

/// Contains implementations and definitions for dealing with paths through a transition system.
pub mod path;
pub use path::Path;

mod sproutable;
pub use sproutable::{IndexedAlphabet, Sproutable};

mod shrinkable;
pub use shrinkable::Shrinkable;

mod deterministic;
pub use deterministic::Deterministic;

/// Implements a type of (nondeterministic) transition system based on a vector of state information and a vector of edges.
pub mod nts;
pub use nts::NTS;

mod builder;
pub use builder::TSBuilder;

mod dts;
pub use dts::{CollectDTS, DTS};

/// Deals with analysing reachability in transition systems.
pub mod reachable;

/// Contains implementations for SCC decompositions and the corresponding/associated types.
pub mod connected_components;

/// In this module, everything concering the run of a transition system on a word is defined.
pub mod run;

/// This module defines traits for dealing with predecessors in a transition system.
pub mod predecessors;

/// Defines directed acyclic graphs (DAG)s and operations on them.
pub mod dag;

/// Encapsulates what is necessary for a type to be usable as a state index in a [`TransitionSystem`].
pub trait IndexType: Copy + std::hash::Hash + std::fmt::Debug + Eq + Ord + Display + Show {
    /// Gives the first possible index. For an integer type, this should be `0`. For a product type,
    /// this should be the product of the first indices of the components.
    fn first() -> Self;
}

impl IndexType for usize {
    fn first() -> Self {
        0
    }
}

impl<I: IndexType, J: IndexType> IndexType for ProductIndex<I, J> {
    fn first() -> Self {
        ProductIndex(I::first(), J::first())
    }
}

/// Implementors of this trait can be transformed into a owned tuple representation of
/// an edge in a [`TransitionSystem`].
pub trait IntoEdge<Idx, E, C> {
    /// Consumes `self` and returns a tuple representing an edge in a [`TransitionSystem`].
    /// Owned edges in their tuple representation may simply be cloned, whereas if we have
    /// a tuple represetation of an edge with a borrowed expression, this operation may
    /// have to clone the expression.
    fn into_edge(self) -> (Idx, E, C, Idx);
}

impl<Idx, E, C: Color> IntoEdge<Idx, E, C> for (Idx, E, C, Idx) {
    fn into_edge(self) -> (Idx, E, C, Idx) {
        self
    }
}

impl<Idx, E, C> IntoEdge<Idx, E, Void> for (Idx, E, C, Idx) {
    fn into_edge(self) -> (Idx, E, Void, Idx) {
        (self.0, self.1, Void, self.3)
    }
}

impl<Idx, E> IntoEdge<Idx, E, Void> for (Idx, E, Idx) {
    fn into_edge(self) -> (Idx, E, Void, Idx) {
        (self.0, self.1, Void, self.2)
    }
}

/// Type alias for extracting the state color in a [`TransitionSystem`].
pub type StateColor<X> = <X as TransitionSystem>::StateColor;
/// Type alias for extracting the edge color in a [`TransitionSystem`].
pub type EdgeColor<X> = <X as TransitionSystem>::EdgeColor;

/// Implementors of this trait have a distinguished (initial) state.
pub trait Pointed: TransitionSystem {
    /// Returns the index of the initial state.
    fn initial(&self) -> Self::StateIndex;

    /// Returns the color of the initial state.
    fn initial_color(&self) -> Self::StateColor {
        self.state_color(self.initial())
            .expect("Initial state must exist and be colored!")
    }
}

impl<P: Pointed> Pointed for &P {
    fn initial(&self) -> Self::StateIndex {
        P::initial(self)
    }
}

impl<P: Pointed> Pointed for &mut P {
    fn initial(&self) -> Self::StateIndex {
        P::initial(self)
    }
}

/// This module deals with transforming a transition system (or similar) into a representation in the dot (graphviz) format.
pub mod dot;
pub use dot::Dottable;

mod quotient;
pub use quotient::Quotient;

use self::{operations::ProductIndex, transition_system::IsEdge};

/// A congruence is a [`TransitionSystem`], which additionally has a distinguished initial state. On top
/// of that, a congruence does not have any coloring on either states or symbols. This
/// functionality is abstracted in [`Pointed`]. This trait is automatically implemented.
pub trait Congruence: Deterministic + Pointed {
    /// Creates a new instance of a [`RightCongruence`] from the transition structure of `self`. Returns
    /// the created congruence together with a [`Map`] from old/original state indices to indices of the
    /// created congruence.
    fn build_right_congruence(
        &self,
    ) -> (
        RightCongruence<Self::Alphabet>,
        Map<Self::StateIndex, usize>,
    ) {
        let mut cong: RightCongruence<Self::Alphabet> =
            RightCongruence::new_for_alphabet(self.alphabet().clone());
        let mut map = Map::default();

        for state in self.state_indices() {
            map.insert(state, cong.add_state(Class::epsilon()));
        }

        for state in self.state_indices() {
            if let Some(it) = self.edges_from(state) {
                for edge in it {
                    let target = edge.target();
                    let target_class = map.get(&target).unwrap();
                    let _color = edge.color().clone();
                    let _target_class = cong.add_edge(
                        *map.get(&state).unwrap(),
                        edge.expression().clone(),
                        *target_class,
                        Void,
                    );
                }
            }
        }

        cong.recompute_labels();

        (cong, map)
    }
}
impl<Sim: Deterministic + Pointed> Congruence for Sim {}

#[cfg(test)]
pub mod tests {}
