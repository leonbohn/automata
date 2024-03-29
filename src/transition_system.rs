use itertools::Itertools;

use crate::{math::Map, math::Partition, prelude::*};
use std::{fmt::Display, hash::Hash};

mod edge;
pub use edge::{Edge, EdgeReference, IsEdge};

mod transitions_from;
pub use transitions_from::{DeterministicEdgesFrom, TransitionsFrom};

/// Defines implementations for common operations on automata/transition systems.
pub mod operations;

/// This module contains the various provided implementations of [`TransitionSystem`]. There are
/// two variants of concern, which differ mainly in the data structure that backs them.
/// - [`NTS`] is a (nondeterministic) transition system which is backed by an edge list. It is
/// efficient for large systems and this implementation is used by default. There is a variant
/// [`DTS`] which is simply a thin wrapper around [`NTS`], indicating that the wrapped transition
/// system is deterministic, i.e. it implements [`Deterministic`].
/// - [`HashTs`] is a (deterministic) transition system which is backed by a [`crate::Set`] of
/// states and a [`crate::math::Map`] of edges. In other words, it uses a hash table internally.
pub mod impls;
pub use impls::{CollectDTS, HashTs, IntoHashTs, DTS, NTS};

/// Contains implementations and definitions for dealing with paths through a transition system.
pub mod path;
pub use path::Path;

mod sproutable;
pub use sproutable::{IndexedAlphabet, Sproutable};

mod shrinkable;
pub use shrinkable::Shrinkable;

mod deterministic;
pub use deterministic::Deterministic;

mod builder;
pub use builder::TSBuilder;

/// Deals with analysing reachability in transition systems.
pub mod reachable;
pub use reachable::{
    MinimalRepresentative, MinimalRepresentatives, ReachableStateIndices, ReachableStates,
};

/// Contains implementations for SCC decompositions and the corresponding/associated types.
pub mod connected_components;
use connected_components::{tarjan_scc_iterative, tarjan_scc_recursive, TarjanDAG};

/// In this module, everything concering the run of a transition system on a word is defined.
pub mod run;

/// This module defines traits for dealing with predecessors in a transition system.
pub mod predecessors;

/// Encapsulates the transition function δ of a (finite) transition system. This is the main trait that
/// is used to query a transition system. Transitions are labeled with a [`Alphabet::Expression`], which
/// determines on which [`Alphabet::Symbol`]s the transition can be taken. Additionally, every transition
/// is labeled with a [`crate::Color`], which can be used to store additional information about it, like an
/// associated priority.
///
/// # The difference between transitions and edges
/// Internally, a transition system is represented as a graph, where the states are the nodes and the
/// transitions are the edges. However, the transitions are not the same as the edges.
/// Both store the source and target vertex as well as the color, however an edge is labelled
/// with an expression, while a transition is labelled with an actual symbol (that [`Alphabet::matches`]
/// the expression). So a transition is a concrete edge that is taken (usually by the run on a word), while
/// an edge may represent any different number of transitions.
pub trait TransitionSystem: Sized {
    /// The type of the underlying [`Alphabet`].
    type Alphabet: Alphabet;
    /// The type of the indices of the states of the transition system.
    type StateIndex: IndexType;
    /// The type of the colors of the states of the transition system.
    type StateColor: Clone;
    /// The type of the colors of the edges of the transition system.
    type EdgeColor: Clone;
    /// The type of the references to the transitions of the transition system.
    type EdgeRef<'this>: IsEdge<'this, ExpressionOf<Self>, Self::StateIndex, EdgeColor<Self>>
    where
        Self: 'this;
    /// The type of the iterator over the transitions that start in a given state.
    type EdgesFromIter<'this>: Iterator<Item = Self::EdgeRef<'this>>
    where
        Self: 'this;
    /// Type of the iterator over the state indices.
    type StateIndices<'this>: Iterator<Item = Self::StateIndex>
    where
        Self: 'this;

    /// Returns a reference to the alphabet of `self`.
    fn alphabet(&self) -> &Self::Alphabet;

    /// Calls the [`Alphabet::universe`] method on the alphabet of `self`, returning
    /// an iterator of all symbols.
    fn symbols(&self) -> <Self::Alphabet as Alphabet>::Universe<'_> {
        self.alphabet().universe()
    }

    /// Returns a vector of all state indices of `self`. By default, this is simply a helper
    /// calling to [`Self::state_indices`], but it can be overridden to provide a more
    /// efficient implementation.
    fn state_indices_vec(&self) -> Vec<Self::StateIndex> {
        self.state_indices().collect()
    }

    /// Returns an iterator over the state indices of `self`.
    fn state_indices(&self) -> Self::StateIndices<'_>;

    /// Returns true if the transition system has no states.
    fn is_stateless(&self) -> bool {
        self.state_indices().next().is_none()
    }

    /// Returns an iterator over pairs consisting of a state index and the corresponding state color.
    fn state_indices_with_color(
        &self,
    ) -> impl Iterator<Item = (Self::StateIndex, Self::StateColor)> {
        self.state_indices()
            .map(|q| (q, self.state_color(q).expect("Every state must be colored")))
    }

    /// Helper function which creates an expression from the given symbol.
    /// This is a convenience function that simply calls [`Alphabet::expression`].
    fn make_expression(&self, sym: SymbolOf<Self>) -> ExpressionOf<Self> {
        <Self::Alphabet as Alphabet>::expression(sym)
    }

    /// Gives an iterator over all transitions of `self`.
    fn transitions(&self) -> impl Iterator<Item = Self::EdgeRef<'_>> {
        self.state_indices().flat_map(move |q| {
            self.edges_from(q)
                .expect("should return iterator for state that exists")
        })
    }

    /// Returns true if the transition system has no edges. This is rather costly, as it
    /// simply iterates over all states and checks whether they have any outgoing edges.
    /// Should be overridden if a more efficient implementation is available.
    fn is_edgeless(&self) -> bool {
        self.state_indices().all(|q| {
            self.edges_from(q)
                .map(|mut it| it.next().is_none())
                .unwrap_or(true)
        })
    }

    /// Returns an iterator giving all colors that are used by the edges of `self`.
    /// Note that this **may output the same color multiple times**, if it is used by multiple
    /// edges. If that is not desired, use [`Self::edge_colors_unique()`] instead.
    ///
    /// A call is rather costly, as it simply iterates over all states and collects the
    /// colors of the outgoing edges. Should be overridden if a more efficient implementation
    /// is available.
    fn edge_colors(&self) -> impl Iterator<Item = Self::EdgeColor>
    where
        EdgeColor<Self>: Clone,
    {
        self.state_indices()
            .flat_map(|q| {
                self.edges_from(q)
                    .expect("should return iterator for state that exists")
            })
            .map(|t| t.color().clone())
    }

    /// Returns an iterator giving all **unique** colors that are used by the edges of `self`.
    /// By default, a call is rather costly as it simply iterates over all states and collects
    /// the colors of the outgoing edges. Should be overridden if a more efficient implementation
    /// is available.
    fn edge_colors_unique(&self) -> impl Iterator<Item = Self::EdgeColor>
    where
        EdgeColor<Self>: Eq + Hash + Clone,
    {
        self.edge_colors().unique()
    }

    /// Returns an iterator over the transitions that start in the given `state`. If the state does
    /// not exist, `None` is returned.
    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>>;

    /// Returns an iterator over all transitions that start in the given `state` and whose expression
    /// matches the given `sym`. If the state does not exist, `None` is returned.
    fn edges_matching<Idx: Indexes<Self>>(
        &self,
        state: Idx,
        sym: SymbolOf<Self>,
    ) -> Option<
        impl Iterator<
            Item = (
                Self::StateIndex,
                &ExpressionOf<Self>,
                Self::EdgeColor,
                Self::StateIndex,
            ),
        >,
    >
    where
        EdgeColor<Self>: Clone,
    {
        let idx = state.to_index(self)?;
        Some(self.edges_from(state)?.filter_map(move |t| {
            if t.expression().matches(sym) {
                Some((idx, t.expression(), t.color().clone(), t.target()))
            } else {
                None
            }
        }))
    }

    /// Returns true if and only if there exists a transition from the given `source` state to the
    /// given `target` state, whose expression is matched by the given `sym`. If either the source
    /// or the target state does not exist, `false` is returned.
    fn has_transition<Idx: Indexes<Self>, Jdx: Indexes<Self>>(
        &self,
        source: Idx,
        sym: SymbolOf<Self>,
        target: Jdx,
    ) -> bool {
        let Some(source) = source.to_index(self) else {
            return false;
        };
        let Some(target) = target.to_index(self) else {
            return false;
        };
        if let Some(mut it) = self.edges_from(source) {
            it.any(|t| t.target() == target && t.expression().matches(sym))
        } else {
            false
        }
    }

    /// Returns an iterator over the transitions that start in the given `state`. Panics if the
    /// state does not exist.
    fn transitions_from<Idx: Indexes<Self>>(&self, state: Idx) -> TransitionsFrom<'_, Self> {
        TransitionsFrom::new(
            self,
            state
                .to_index(self)
                .expect("Should only be called for states that exist!"),
        )
    }

    /// Commence a new subset construction starting from the collection of states given by `states`.
    /// This is a convenience function that simply calls [`operations::SubsetConstruction::new`]. It produces a
    /// deterministic transition system operating on sets of states.
    fn subset_construction_from<I: IntoIterator<Item = Self::StateIndex>>(
        self,
        states: I,
    ) -> operations::SubsetConstruction<Self> {
        operations::SubsetConstruction::new(self, states)
    }

    /// Performs a subset construction using [`Self::subset_construction_from`] starting with a singleton
    /// set containing the only initial state of `self`.
    fn subset_construction(self) -> operations::SubsetConstruction<Self>
    where
        Self: Pointed,
    {
        let initial = self.initial();
        operations::SubsetConstruction::new_from(self, initial)
    }

    /// Returns the color of the given `state`, if it exists. Otherwise, `None` is returned.
    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor>;

    /// Attempts to find a word which leads from the state `from` to state `to`. If no such
    /// word exists, `None` is returned.
    fn word_from_to<Idx: Indexes<Self>, Jdx: Indexes<Self>>(
        &self,
        from: Idx,
        to: Jdx,
    ) -> Option<Vec<SymbolOf<Self>>>
    where
        Self: Sized,
    {
        let from = from.to_index(self)?;
        let to = to.to_index(self)?;

        self.minimal_representatives_from(from)
            .find_map(|(word, state)| if state == to { Some(word) } else { None })
    }

    /// Gives the size of `self`, which is obtained simply by counting the number of elements yielded by [`Self::state_indices()`].
    fn size(&self) -> usize {
        self.state_indices().count()
    }

    /// Returns `true` if and only if there exists at least one state.
    fn is_empty(&self) -> bool {
        self.size() == 0
    }

    /// Tries to return the index of the state identified by `state`. If the state does not exist,
    /// `None` is returned.
    fn find_state_index<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateIndex> {
        state.to_index(self)
    }

    /// Returns true if and only if the given state `index` exists.
    fn contains_state_index(&self, index: Self::StateIndex) -> bool {
        self.state_indices().contains(&index)
    }

    /// Tries to find the index of a state with the given `color`. Note that this uses `find` and thus
    /// returns the first such state that is found. There is no guarantee on the order in which the states
    /// are visited such that if more than one state with the given `color` exists, subsequent calls to
    /// this method may return different indices.
    fn find_by_color(&self, color: &StateColor<Self>) -> Option<Self::StateIndex>
    where
        StateColor<Self>: Eq,
    {
        self.state_indices()
            .find(|index| self.state_color(*index).as_ref() == Some(color))
    }

    /// Returns true if and only if a state with the given `color` exists.
    fn contains_state_color(&self, color: &StateColor<Self>) -> bool
    where
        StateColor<Self>: Eq,
    {
        self.find_by_color(color).is_some()
    }

    /// Obtains the [`Self::StateIndex`] of a state if it can be found. See [`Indexes`]
    /// for more.
    fn get<Idx: Indexes<Self>>(&self, elem: Idx) -> Option<Self::StateIndex>
    where
        Self: Sized,
    {
        elem.to_index(self)
    }

    /// Returns a [`Initialized`] wrapper around `self`, which designates the given `initial` state.
    /// Note that this function does not (yet) ensure that the index actually exists!
    fn with_initial<Idx: Indexes<Self>>(self, initial: Idx) -> Initialized<Self>
    where
        Self: Sized,
    {
        let initial = initial
            .to_index(&self)
            .expect("Cannot set initial state that does not exist");
        assert!(
            self.contains_state_index(initial),
            "Cannot set initial state that does not exist"
        );
        (self, initial).into()
    }

    /// Builds the [`operations::Quotient`] of `self` with regard to some given [`Partition`].
    fn quotient(self, partition: Partition<Self::StateIndex>) -> operations::Quotient<Self>
    where
        Self: Sized,
    {
        operations::Quotient::new(self, partition)
    }

    /// Restricts the edges of `self` such that only transitions p --a|c--> q exist where
    /// `min` <= `c` <= `max`, i.e. all transitions where either `c` < `min` or `max` < `c`
    /// are discarded.
    fn edge_color_restricted(
        self,
        min: Self::EdgeColor,
        max: Self::EdgeColor,
    ) -> operations::ColorRestricted<Self> {
        operations::ColorRestricted::new(self, min, max)
    }

    /// Restricts the state indices with the given function. This means that only the states for
    /// which the function returns `true` are kept, while all others are removed.
    fn restrict_state_indices<F>(self, filter: F) -> operations::RestrictByStateIndex<Self, F>
    where
        Self: Sized,
        F: operations::StateIndexFilter<Self::StateIndex>,
    {
        operations::RestrictByStateIndex::new(self, filter)
    }

    /// Recolors the edges of `self` with the given function `f`. This works akin to
    /// [`Self::map_edge_colors()`] but allows for a more fine-grained control over the
    /// recoloring process, by giving access not only to the color itself, but also to
    /// the origin, target and expression of the respective edge.
    fn map_edge_colors_full<D, F>(self, f: F) -> operations::MapEdges<Self, F>
    where
        F: Fn(Self::StateIndex, &ExpressionOf<Self>, Self::EdgeColor, Self::StateIndex) -> D,
        D: Clone,
        Self: Sized,
    {
        operations::MapEdges::new(self, f)
    }

    /// Completely removes the edge coloring.
    fn erase_edge_colors(self) -> operations::MapEdgeColor<Self, fn(Self::EdgeColor) -> Void>
    where
        Self: Sized,
    {
        self.map_edge_colors(|_| Void)
    }

    /// Completely removes the state coloring.
    fn erase_state_colors(self) -> operations::MapStateColor<Self, fn(Self::StateColor) -> Void>
    where
        Self: Sized,
    {
        self.map_state_colors(|_| Void)
    }

    /// Map the edge colors of `self` with the given function `f`.
    fn map_edge_colors<D: Clone, F: Fn(Self::EdgeColor) -> D>(
        self,
        f: F,
    ) -> operations::MapEdgeColor<Self, F>
    where
        Self: Sized,
    {
        operations::MapEdgeColor::new(self, f)
    }

    /// Map the state colors of `self` with the given function.
    fn map_state_colors<D: Clone, F: Fn(Self::StateColor) -> D>(
        self,
        f: F,
    ) -> operations::MapStateColor<Self, F>
    where
        Self: Sized,
    {
        operations::MapStateColor::new(self, f)
    }

    /// Turns `self` into a DFA that accepts all words, i.e. all states are accepting.
    fn all_accepting_dfa(self) -> operations::MapStateColor<Self, fn(Self::StateColor) -> bool>
    where
        Self: Sized,
    {
        self.map_state_colors(|_| true)
    }

    /// Obtains the [`connected_components::SccDecomposition`] of self, which is a partition of the states into strongly
    /// connected components. Uses Tarjan's algorithm.
    fn sccs(&self) -> connected_components::SccDecomposition<'_, Self>
    where
        Self: Sized,
    {
        tarjan_scc_iterative(self)
    }

    /// Obtains the [`connected_components::SccDecomposition`] of self, which is a partition of the states into strongly
    /// connected components. Uses Tarjan's algorithm.
    fn sccs_recursive(&self) -> connected_components::SccDecomposition<'_, Self>
    where
        Self: Sized,
    {
        tarjan_scc_recursive(self)
    }

    /// Obtains the [`TarjanDAG`] of self, which is a directed acyclic graph that represents the
    /// strongly connected components of the transition system and the edges between them.
    fn tarjan_dag(&self) -> TarjanDAG<'_, Self>
    where
        Self: Sized,
    {
        TarjanDAG::from(tarjan_scc_iterative(self))
    }

    /// Obtains the [`TarjanDAG`] of self, which is a directed acyclic graph that represents the
    /// strongly connected components of the transition system and the edges between them.
    fn tarjan_dag_recursive(&self) -> TarjanDAG<'_, Self>
    where
        Self: Sized,
    {
        TarjanDAG::from(tarjan_scc_recursive(self))
    }

    /// Returns `true` iff the given state is reachable from the initial state.
    fn is_reachable<Idx: Indexes<Self>>(&self, state: Idx) -> bool
    where
        Self: Sized + Pointed,
    {
        let Some(state) = state.to_index(self) else {
            return false;
        };
        self.is_reachable_from(self.initial(), state)
    }

    /// Returns `true` iff the given `state` is reachable from the given `origin` state.
    fn is_reachable_from<Idx: Indexes<Self>, Jdx: Indexes<Self>>(
        &self,
        origin: Idx,
        state: Jdx,
    ) -> bool
    where
        Self: Sized + Pointed,
    {
        let Some(origin) = origin.to_index(self) else {
            tracing::error!("Origin state does not exist");
            return false;
        };
        let Some(state) = state.to_index(self) else {
            tracing::error!("Target state does not exist");
            return false;
        };
        self.reachable_state_indices_from(origin)
            .any(|s| s == state)
    }

    /// Returns an iterator over the minimal representative (i.e. length-lexicographically minimal
    /// word reaching the state) of each state that is reachable from the initial state.
    fn minimal_representatives(&self) -> MinimalRepresentatives<&Self>
    where
        Self: Sized + Pointed,
    {
        MinimalRepresentatives::new(self, self.initial())
    }

    /// Returns an iterator over the indices of the states that are reachable from the initial state. The iterator yields tuples
    /// (State Index, State Color)
    fn reachable_states(&self) -> ReachableStates<&Self>
    where
        Self: Sized + Pointed,
    {
        ReachableStates::new(self, self.initial())
    }

    /// Returns an iterator over all state colors that are reachable from the initial state. May yield the same color multiple times.
    fn reachable_state_colors(&self) -> impl Iterator<Item = Self::StateColor>
    where
        Self: Sized + Pointed,
    {
        self.reachable_states().map(|(_, c)| c)
    }

    /// Returns an iterator over the minimal representatives (i.e. length-lexicographically minimal
    /// word reaching the state) of each state that is reachable from the given `state`.
    fn minimal_representatives_from<Idx: Indexes<Self>>(
        &self,
        state: Idx,
    ) -> MinimalRepresentatives<&Self>
    where
        Self: Sized,
    {
        MinimalRepresentatives::new(
            self,
            state
                .to_index(self)
                .expect("cannot comput minimal representatives from non-existing state"),
        )
    }

    /// Returns an iterator over the indices of the states that are reachable from the initial state.
    fn reachable_state_indices(&self) -> ReachableStateIndices<&Self>
    where
        Self: Sized + Pointed,
    {
        self.reachable_state_indices_from(self.initial())
    }

    /// Returns an iterator over the indices of the states that are reachable from the given `state`.
    fn reachable_state_indices_from<Idx: Indexes<Self>>(
        &self,
        state: Idx,
    ) -> ReachableStateIndices<&Self>
    where
        Self: Sized,
    {
        let origin = state
            .to_index(self)
            .expect("Can only run this from a state that exists");
        ReachableStateIndices::new(self, origin)
    }

    /// Returns an iterator over the states that are reachable from the given `state`.
    fn reachable_states_from<Idx: Indexes<Self>>(&self, state: Idx) -> ReachableStates<&Self>
    where
        Self: Sized,
    {
        ReachableStates::new(self, state.to_index(self).unwrap())
    }

    /// Returns an option containing the index of the initial state, if it exists.
    /// This is a somewhat hacky way of dealing with the fact that we cannot express
    /// negative trait bounds. In particular, we cannot express that a transition system
    /// is not pointed, which prevents us from correctly implementing e.g. the `ToDot`
    /// trait for non-pointed transition systems. This function is a workaround for this
    /// problem, as it allows us to check whether a transition system is pointed or not,
    /// since the provided default implementation assumes that the no initial state exists.
    fn maybe_initial_state(&self) -> Option<Self::StateIndex> {
        None
    }
}

impl<Ts: TransitionSystem> TransitionSystem for &Ts {
    type Alphabet = Ts::Alphabet;

    type StateIndex = Ts::StateIndex;

    type StateColor = Ts::StateColor;

    type EdgeColor = Ts::EdgeColor;

    type EdgeRef<'this> = Ts::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this> = Ts::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this> = Ts::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        Ts::alphabet(self)
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        Ts::state_indices(self)
    }

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        Ts::edges_from(self, state.to_index(self)?)
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        Ts::state_color(self, state.to_index(self)?)
    }
}

impl<Ts: TransitionSystem> TransitionSystem for &mut Ts {
    type Alphabet = Ts::Alphabet;

    type StateIndex = Ts::StateIndex;

    type StateColor = Ts::StateColor;

    type EdgeColor = Ts::EdgeColor;

    type EdgeRef<'this> = Ts::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this> = Ts::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this> = Ts::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        Ts::alphabet(self)
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        Ts::state_indices(self)
    }

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        Ts::edges_from(self, state.to_index(self)?)
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        Ts::state_color(self, state.to_index(self)?)
    }
}

/// Trait that helps with accessing states in more elaborate [`TransitionSystem`]s. For
/// example in a [`crate::RightCongruence`], we have more information than the [`crate::Color`]
/// on a state, we have its [`crate::Class`] as well. Since we would like to be able to
/// access a state of a congruence not only by its index, but also by its classname
/// or any other [word](`crate::prelude::LinearWord`) of finite length, this trait is necessary.
///
/// Implementors should be able to _uniquely_ identify a single state in a transition
/// system of type `Ts`.
pub trait Indexes<Ts: TransitionSystem> {
    /// _Uniquely_ identifies a state in `ts` and return its index. If the state does
    /// not exist, `None` is returned.
    fn to_index(&self, ts: &Ts) -> Option<Ts::StateIndex>;
}

impl<Ts: TransitionSystem> Indexes<Ts> for Ts::StateIndex {
    #[inline(always)]
    fn to_index(&self, _ts: &Ts) -> Option<<Ts as TransitionSystem>::StateIndex> {
        Some(*self)
    }
}
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

impl<Idx, E, C, X: IntoEdge<Idx, E, C>> IntoEdge<Idx, E, C> for &X
where
    X: Clone,
{
    fn into_edge(self) -> (Idx, E, C, Idx) {
        X::into_edge(self.clone())
    }
}

/// Helper trait for extracting the [`crate::alphabet::Symbol`] type from an a transition system.
pub type SymbolOf<A> = <<A as TransitionSystem>::Alphabet as Alphabet>::Symbol;
/// Helper trait for extracting the [`Expression`] type from an a transition system.
pub type ExpressionOf<A> = <<A as TransitionSystem>::Alphabet as Alphabet>::Expression;
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
