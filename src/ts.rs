use itertools::Itertools;
use std::borrow::Cow;
use tracing::trace;

use crate::{
    Color, Show, Void,
    alphabet::{Alphabet, Expression},
    partition::Partition,
};
use crate::{DTS, congruence::StateNaming};
use std::{collections::BTreeSet, hash::Hash};

mod state_index;
pub use state_index::{DenseId, EdgeId, IdType};

mod id_collections;
pub use id_collections::{CompactIdMap, StateMap, StateSet, StateSetIter};

mod edge;
pub use edge::EdgeRef;

mod transitions_from;
pub use transitions_from::{DeterministicEdgesFrom, TransitionsFrom};

/// Defines implementations for common operations on automata/transition systems.
pub mod operations;

/// This module contains the various provided implementations of [`crate::TransitionSystem`].
pub(crate) mod impls;
pub use impls::{Compaction, DefaultIdType, DenseTs, Det, LinkedTs};

mod storage;
pub use storage::{Linked, Storage};

/// Contains implementations and definitions for dealing with paths through a transition system.
pub mod path;
pub use path::Path;

mod sproutable;
pub use sproutable::{ForAlphabet, Sproutable};

mod shrinkable;
pub use shrinkable::Shrinkable;

mod deterministic;
pub use deterministic::Deterministic;

mod builder;
pub use builder::{Builder, BuilderError};

/// Deals with analysing reachability in transition systems.
pub mod visit;
pub use visit::{AccessWords, Bfs, BfsEdges, Dfs, LengthLexicographicMinimalRepresentatives};

/// Contains implementations for SCC decompositions and the corresponding/associated types.
pub mod connected_components;
use connected_components::{SccDecomposition, tarjan_scc_iterative, tarjan_scc_recursive};

/// In this module, everything concering the run of a transition system on a word is defined.
pub mod run;

/// This module defines traits for dealing with predecessors in a transition system.
pub mod predecessors;

mod word_as_ts;

/// Naive reference model for model-based tests of the storages.
#[cfg(test)]
mod model;

pub use crate::ts::predecessors::PredecessorIterable;
pub use word_as_ts::WordTs;

/// Encapsulates the transition function δ of a transition system. This is the main trait that
/// is used to query a transition system.
///
/// It only requires that the outgoing edges of a state and that state's color can be computed,
/// so systems that are explored lazily (subset constructions, products) can implement it.
/// Everything that needs to enumerate all states lives in the subtrait [`States`] instead.
///
/// Transitions are labeled with an [`Alphabet::Expression`], which determines on which
/// [`Alphabet::Symbol`]s the transition can be taken. Additionally, every transition
/// is labeled with a [`crate::Color`], which can be used to store additional information about it,
/// like an associated priority.
///
/// # The difference between transitions and edges
/// Internally, a transition system is represented as a graph, where the states are the nodes and the
/// transitions are the edges. However, the transitions are not the same as the edges.
/// Both store the source and target vertex as well as the color, however an edge is labelled
/// with an expression, while a transition is labelled with an actual symbol (that [`crate::alphabet::Matcher::matches`]
/// the expression). So a transition is a concrete edge that is taken (usually by the run on a word), while
/// an edge may represent any different number of transitions.
pub trait TransitionSystem: Sized {
    /// The type of the underlying [`Alphabet`].
    type Alphabet: Alphabet;

    /// The type of the indices of the states of the transition system.
    type StateIndex: IdType;

    /// The type of the colors of the states of the transition system.
    type StateColor: Color;

    /// The type of the colors of the edges of the transition system.
    type EdgeColor: Color;

    /// The type of the iterator over the transitions that start in a given state.
    type EdgesFromIter<'this>: Iterator<Item = EdgeOf<'this, Self>>
    where
        Self: 'this;

    /// Returns an iterator over the transitions that start in the given `state`. If the state does
    /// not exist, `None` is returned.
    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>>;

    /// Returns a reference to the alphabet of `self`.
    fn alphabet(&self) -> &Self::Alphabet;

    /// Calls the [`Alphabet::universe`] method on the alphabet of `self`, returning
    /// an iterator of all symbols.
    #[inline(always)]
    fn symbols(&self) -> <Self::Alphabet as Alphabet>::Universe<'_> {
        self.alphabet().universe()
    }

    /// Returns an iterator over the indices of the successors of the given state, if it exists.
    /// Otherwise, the method returns `None`.
    ///
    /// Might produce duplicates.
    fn successor_indices(
        &self,
        state: StateIndex<Self>,
    ) -> Option<impl Iterator<Item = StateIndex<Self>>> {
        Some(self.edges_from(state)?.map(|edge| edge.target()))
    }

    /// Consumes `self` and sets the given `initial` to be the designated initial state. This constructs
    /// an instance of [`crate::automaton::WithInitial`] which is in turn simply an [`crate::Automaton`]
    /// without semantics.
    fn with_initial(self, initial: Self::StateIndex) -> crate::automaton::WithInitial<Self>
    where
        Self: Sized,
    {
        crate::automaton::WithInitial::from_parts(self, initial)
    }

    /// Returns true if and only if there exists a transition from the given `source` state to the
    /// given `target` state, whose expression is matched by the given `sym`. If either the source
    /// or the target state does not exist, `false` is returned.
    fn has_transition(
        &self,
        source: StateIndex<Self>,
        sym: SymbolOf<Self>,
        target: StateIndex<Self>,
    ) -> bool {
        if let Some(mut it) = self.edges_from(source) {
            it.any(|t| t.target() == target && t.expression().matched_by(sym))
        } else {
            false
        }
    }

    /// Returns an iterator over the transitions that start in the given `state`, or `None` if
    /// the state does not exist.
    fn transitions_from(&self, state: StateIndex<Self>) -> Option<TransitionsFrom<'_, Self>> {
        TransitionsFrom::new(self, state)
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
    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>>;

    /// Returns an exclusive upper bound on the dense ids of the states, i.e. every state id `q`
    /// with `q.to_dense() == Some(n)` satisfies `n < bound`. Returns `None` if there is no such
    /// bound, e.g. for lazily explored systems. Algorithms use it to choose between dense
    /// (bitsets, vectors) and sparse (hash based) containers, see [`StateSet`] and [`StateMap`].
    ///
    /// A bound must be *tight*: consumers eagerly allocate dense containers sized by it
    /// ([`StateSet::new`] reserves `bound` bits up front), so a bound that is sound but huge,
    /// such as `2^n` for a subset construction over `n` states, is worse than returning `None`.
    /// Only report a bound that is of the order of the number of states that will actually be
    /// visited.
    fn state_bound(&self) -> Option<usize> {
        None
    }

    /// Attempts to find a word which leads from the state `from` to state `to`. If no such
    /// word exists, `None` is returned.
    fn word_from_to(
        &self,
        from: StateIndex<Self>,
        to: StateIndex<Self>,
    ) -> Option<Vec<SymbolOf<Self>>>
    where
        Self: Sized,
    {
        AccessWords::new(self, from).word_to(to)
    }

    /// Restricts the edges of `self` such that only transitions p --a|c--> q exist where
    /// `min` <= `c` <= `max`, i.e. all transitions where either `c` < `min` or `max` < `c`
    /// are discarded.
    #[inline(always)]
    fn edge_color_restricted(
        self,
        min: Self::EdgeColor,
        max: Self::EdgeColor,
    ) -> operations::EdgeColorRestricted<Self> {
        operations::EdgeColorRestricted::new(self, min, max)
    }

    /// Restricts the state indices with the given function. This means that only the states for
    /// which the function returns `true` are kept, while all others are removed.
    #[inline(always)]
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
    ///
    /// Like the adapters of [`Iterator`], this is **lazy**: `f` runs whenever a color is
    /// accessed and nothing is cached. Use `collect` to materialize the result.
    #[inline(always)]
    fn map_edge_colors_full<D, F>(
        self,
        f: F,
    ) -> operations::Recolor<Self, operations::Keep, operations::EdgeFn<F>>
    where
        F: Fn(Self::StateIndex, &EdgeExpression<Self>, Self::EdgeColor, Self::StateIndex) -> D,
        D: Color,
        Self: Sized,
    {
        operations::Recolor::new(self, operations::Keep, operations::EdgeFn(f))
    }

    /// Removes all coloring from `self`, giving a transition system that has edges and states
    /// colored with type [`Void`].
    #[inline(always)]
    fn erase_colors(self) -> operations::EraseColors<Self>
    where
        Self: Sized,
    {
        operations::Recolor::new(
            self,
            operations::StateColorFn((|_| Void) as fn(Self::StateColor) -> Void),
            operations::ColorFn((|_| Void) as fn(Self::EdgeColor) -> Void),
        )
    }

    /// Completely removes the edge coloring.
    #[inline(always)]
    fn erase_edge_colors(self) -> operations::EraseEdgeColors<Self>
    where
        Self: Sized,
    {
        self.map_edge_colors(|_| Void)
    }

    /// Completely removes the state coloring.
    #[inline(always)]
    fn erase_state_colors(self) -> operations::EraseStateColors<Self>
    where
        Self: Sized,
    {
        operations::Recolor::new(
            self,
            operations::StateColorFn((|_| Void) as fn(Self::StateColor) -> Void),
            operations::Keep,
        )
    }

    /// Map the edge colors of `self` with the given function `f`.
    ///
    /// Like [`Iterator::map`], this is **lazy**: `f` runs whenever a color is accessed and
    /// nothing is cached. Use `collect` to materialize the result.
    #[inline(always)]
    fn map_edge_colors<D: Color, F: Fn(Self::EdgeColor) -> D>(
        self,
        f: F,
    ) -> operations::Recolor<Self, operations::Keep, operations::ColorFn<F>>
    where
        Self: Sized,
    {
        operations::Recolor::new(self, operations::Keep, operations::ColorFn(f))
    }

    /// Consumes and recolors `self` with the colors as given by `provider`.
    /// See more possible ways of assigning colors in [`operations::ProvidesStateColor`].
    ///
    /// # Example
    /// ```
    /// use automata::ts::{Builder, Deterministic, operations::UniformColor, TransitionSystem};
    ///
    /// let ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 1), (1, 'a', 2), (2, 'a', 0)])
    ///     .into_dts_with_initial(0);
    /// let colored = ts.with_state_color(UniformColor(false));
    /// assert_eq!(colored.run("a").reached_state_color(), Some(false));
    /// assert_eq!(colored.with_state_color(UniformColor(true)).run("a").reached_state_color(), Some(true));
    /// ```
    #[inline(always)]
    fn with_state_color<P: ProvidesStateColor<Self::StateIndex>>(
        self,
        provider: P,
    ) -> operations::Recolor<Self, operations::Provided<P>, operations::Keep>
    where
        Self: Sized,
    {
        operations::Recolor::new(self, operations::Provided(provider), operations::Keep)
    }

    /// Map the state colors of `self` with the given function.
    ///
    /// Like [`Iterator::map`], this is **lazy**: `f` runs whenever a color is accessed and
    /// nothing is cached. Use `collect` to materialize the result.
    #[inline(always)]
    fn map_state_colors<D: Color, F: Fn(Self::StateColor) -> D>(
        self,
        f: F,
    ) -> operations::Recolor<Self, operations::StateColorFn<F>, operations::Keep>
    where
        Self: Sized,
    {
        operations::Recolor::new(self, operations::StateColorFn(f), operations::Keep)
    }

    /// Computes the [`connected_components::SccDecomposition`] of self, restricted
    /// to the set of vertices that is given.
    #[inline(always)]
    fn reachable_sccs_from<I: IntoIterator<Item = StateIndex<Self>>>(
        &self,
        from: I,
    ) -> SccDecomposition<'_, Self>
    where
        Self: Sized,
    {
        connected_components::tarjan_scc_iterative_from(self, from)
    }

    /// Performs an SCC decomposition of self using Kosaraju's algorithm, starting from the state `start`. This is an
    /// efficient algorithm and it might provide more performance over Tarjan's algorithm in some cases.
    fn sccs_kosaraju(&self, start: Self::StateIndex) -> SccDecomposition<'_, Self>
    where
        Self: Sized,
        Self: PredecessorIterable,
    {
        connected_components::kosaraju(self, start)
    }

    /// Returns `true` iff the given `state` is reachable from the given `origin` state.
    fn is_reachable_from(&self, origin: StateIndex<Self>, state: StateIndex<Self>) -> bool
    where
        Self: Sized,
    {
        self.reachable_state_indices_from(origin)
            .any(|s| s == state)
    }

    /// Gives a canonical state naming for the states of `self`, based
    /// on the minimal repesentatives of the states.
    fn canonical_naming(&self) -> StateNaming<Self>
    where
        Self: Sized + Pointed,
    {
        self.canonical_naming_from(self.initial())
    }

    /// Gives a canonical state naming for the states of `self` with
    /// respect to the given starting state. See [`Self::canonical_naming`].
    fn canonical_naming_from(&self, origin: StateIndex<Self>) -> StateNaming<Self>
    where
        Self: Sized + Pointed,
    {
        StateNaming::from_iter(self.minimal_representatives_iter_from(origin))
    }

    /// Returns an iterator over the minimal representative (i.e. length-lexicographically minimal
    /// word reaching the state) of each state that is reachable from the initial state.
    fn minimal_representatives_iter(&self) -> LengthLexicographicMinimalRepresentatives<'_, Self>
    where
        Self: Sized + Pointed,
    {
        LengthLexicographicMinimalRepresentatives::new(self, self.initial())
    }

    /// Returns an iterator over the minimal representatives (i.e. length-lexicographically minimal
    /// word reaching the state) of each state that is reachable from the given `state`.
    fn minimal_representatives_iter_from(
        &self,
        state: StateIndex<Self>,
    ) -> LengthLexicographicMinimalRepresentatives<'_, Self> {
        LengthLexicographicMinimalRepresentatives::new(self, state)
    }

    /// Returns an iterator over the indices of the states that are reachable from the initial state.
    fn reachable_state_indices(&self) -> Bfs<'_, Self>
    where
        Self: Sized + Pointed,
    {
        self.reachable_state_indices_from(self.initial())
    }

    /// Returns an iterator over the indices of the states that are reachable from the given `state`.
    fn reachable_state_indices_from(&self, state: Self::StateIndex) -> Bfs<'_, Self>
    where
        Self: Sized,
    {
        Bfs::new(self, state)
    }

    /// Returns an iterator over the edges that are reachable from the given `state`.
    fn reachable_edges_from(&self, state: StateIndex<Self>) -> BfsEdges<'_, Self>
    where
        Self: Sized,
    {
        BfsEdges::new(self, state)
    }
}

/// Finite transition systems whose states can be enumerated.
///
/// [`TransitionSystem`] only requires that the successors of a given state can be computed,
/// which is all that is needed to follow runs or to explore what is reachable from a state.
/// Systems that are computed lazily, like a subset construction or a product, cannot cheaply
/// list all of their states and therefore only implement [`TransitionSystem`]. Everything
/// that needs to see all states (SCC decompositions, quotients, collecting into a
/// stored system, ...) is bounded on this trait instead.
pub trait States: TransitionSystem {
    /// Type of the iterator over the state indices.
    type StatesIter<'this>: Iterator<Item = Self::StateIndex>
    where
        Self: 'this;

    /// Returns an iterator over the state indices of `self`.
    fn states(&self) -> Self::StatesIter<'_>;

    /// Returns true if the transition system has no states.
    fn has_no_states(&self) -> bool {
        self.states().next().is_none()
    }

    /// Returns an iterator over pairs consisting of a state index and the corresponding state color.
    fn states_with_color(&self) -> impl Iterator<Item = (Self::StateIndex, Self::StateColor)> {
        self.states().map(|q| {
            (
                q,
                self.state_color(q)
                    .expect("Every state must be colored")
                    .into_owned(),
            )
        })
    }

    /// Gives an iterator over all transitions of `self`.
    fn transitions(&self) -> impl Iterator<Item = EdgeOf<'_, Self>> {
        self.states().flat_map(move |q| {
            self.edges_from(q)
                .expect("should return iterator for state that exists")
        })
    }

    /// Returns true if the transition system has no edges. This is rather costly, as it
    /// simply iterates over all states and checks whether they have any outgoing edges.
    /// Should be overridden if a more efficient implementation is available.
    fn is_edgeless(&self) -> bool {
        self.states().all(|q| {
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
        self.states()
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

    /// Returns true if the transition system is deterministic, i.e. if there are no two edges leaving
    /// the same state with the same symbol.
    fn is_deterministic(&self) -> bool {
        for state in self.states() {
            let edges: Vec<_> = self.edges_from(state).unwrap().collect();
            for (i, l) in edges.iter().enumerate() {
                for r in &edges[i + 1..] {
                    if self.alphabet().overlapping(l.expression(), r.expression()) {
                        trace!(
                            "found overlapping edges from {:?}: on {} to {:?} and on {} to {:?}",
                            l.source(),
                            l.expression().show(),
                            l.target(),
                            r.expression().show(),
                            r.target(),
                        );
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Checks whether `self` is complete, meaning every state has a transition for every symbol
    /// of the alphabet.
    fn is_complete(&self) -> bool {
        let universe = self.alphabet().universe().collect::<BTreeSet<_>>();

        for q in self.states() {
            let syms = self
                .transitions_from(q)
                .into_iter()
                .flatten()
                .map(|(_q, a, _c, _p)| a)
                .collect::<BTreeSet<_>>();

            assert!(
                syms.is_subset(&universe),
                "Makes no sense to have more symbols on transitions than in the alphabet"
            );
            if !universe.is_subset(&syms) {
                return false;
            }
        }
        true
    }

    /// Returns the number of states of `self`, obtained by counting the elements yielded by [`Self::states`].
    fn state_count(&self) -> usize {
        self.states().count()
    }

    /// Returns true if and only if the given state `index` exists.
    #[inline(always)]
    fn contains_state(&self, index: Self::StateIndex) -> bool {
        self.states().contains(&index)
    }

    /// Tries to find the index of a state with the given `color`. Note that this uses `find` and thus
    /// returns the first such state that is found. There is no guarantee on the order in which the states
    /// are visited such that if more than one state with the given `color` exists, subsequent calls to
    /// this method may return different indices.
    #[inline(always)]
    fn find_by_color(&self, color: &StateColor<Self>) -> Option<Self::StateIndex>
    where
        StateColor<Self>: Eq,
    {
        self.states()
            .find(|index| self.state_color(*index).as_deref() == Some(color))
    }

    /// Returns true if and only if a state with the given `color` exists.
    #[inline(always)]
    fn contains_state_color(&self, color: &StateColor<Self>) -> bool
    where
        StateColor<Self>: Eq,
    {
        self.find_by_color(color).is_some()
    }

    /// Builds the [`operations::Quotient`] of `self` with regard to some given [`Partition`].
    #[inline(always)]
    fn quotient(self, partition: Partition<Self::StateIndex>) -> operations::Quotient<Self>
    where
        Self: Sized,
    {
        operations::Quotient::new(self, partition)
    }

    /// Obtains the [`connected_components::SccDecomposition`] of self, which is a partition of the states into strongly
    /// connected components. Uses Tarjan's algorithm.
    #[inline(always)]
    fn sccs(&self) -> SccDecomposition<'_, Self>
    where
        Self: Sized,
    {
        tarjan_scc_iterative(self)
    }

    /// Obtains the [`connected_components::SccDecomposition`] of self, which is a partition of the states into strongly
    /// connected components. Uses Tarjan's algorithm.
    fn sccs_recursive(&self) -> SccDecomposition<'_, Self>
    where
        Self: Sized,
    {
        tarjan_scc_recursive(self)
    }
}

impl<Ts: TransitionSystem> TransitionSystem for &Ts {
    type Alphabet = Ts::Alphabet;

    type StateIndex = Ts::StateIndex;

    type StateColor = Ts::StateColor;

    type EdgeColor = Ts::EdgeColor;

    type EdgesFromIter<'this>
        = Ts::EdgesFromIter<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        Ts::alphabet(self)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Ts::edges_from(self, state)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        Ts::state_color(self, state)
    }

    fn state_bound(&self) -> Option<usize> {
        Ts::state_bound(self)
    }
}

impl<Ts: TransitionSystem> TransitionSystem for &mut Ts {
    type Alphabet = Ts::Alphabet;

    type StateIndex = Ts::StateIndex;

    type StateColor = Ts::StateColor;

    type EdgeColor = Ts::EdgeColor;

    type EdgesFromIter<'this>
        = Ts::EdgesFromIter<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        Ts::alphabet(self)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Ts::edges_from(self, state)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        Ts::state_color(self, state)
    }

    fn state_bound(&self) -> Option<usize> {
        Ts::state_bound(self)
    }
}

impl<Ts: States> States for &Ts {
    type StatesIter<'this>
        = Ts::StatesIter<'this>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        Ts::states(self)
    }

    fn state_count(&self) -> usize {
        Ts::state_count(self)
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        Ts::contains_state(self, index)
    }
}

impl<Ts: States> States for &mut Ts {
    type StatesIter<'this>
        = Ts::StatesIter<'this>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        Ts::states(self)
    }

    fn state_count(&self) -> usize {
        Ts::state_count(self)
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        Ts::contains_state(self, index)
    }
}

/// Implementors of this trait can be transformed into a owned tuple representation of
/// an edge in a [`TransitionSystem`].
pub trait IntoEdgeTuple<Ts: TransitionSystem> {
    /// Consumes `self` and returns a tuple representing an edge in a [`TransitionSystem`].
    /// Owned edges in their tuple representation may simply be cloned, whereas if we have
    /// a tuple represetation of an edge with a borrowed expression, this operation may
    /// have to clone the expression.
    fn into_edge_tuple(self) -> EdgeTuple<Ts>;
}

impl<T: TransitionSystem> IntoEdgeTuple<T> for EdgeTuple<T> {
    #[inline(always)]
    fn into_edge_tuple(self) -> EdgeTuple<T> {
        self
    }
}

impl<T: TransitionSystem<EdgeColor = Void>> IntoEdgeTuple<T>
    for (StateIndex<T>, EdgeExpression<T>, StateIndex<T>)
{
    #[inline(always)]
    fn into_edge_tuple(self) -> EdgeTuple<T> {
        (self.0, self.1, Void, self.2)
    }
}

impl<T: TransitionSystem, TT: IntoEdgeTuple<T>> IntoEdgeTuple<T> for &TT
where
    TT: Clone,
{
    #[inline(always)]
    fn into_edge_tuple(self) -> EdgeTuple<T> {
        self.clone().into_edge_tuple()
    }
}

/// Helper trait for extracting the [`crate::alphabet::Symbol`] type from an a transition system.
pub type SymbolOf<A> = <<A as TransitionSystem>::Alphabet as Alphabet>::Symbol;
/// Helper trait for extracting the [`crate::alphabet::Expression`] type from an a transition system.
pub type EdgeExpression<A> = <<A as TransitionSystem>::Alphabet as Alphabet>::Expression;
/// Type alias for extracting the state color in a [`TransitionSystem`].
pub type StateColor<X> = <X as TransitionSystem>::StateColor;
/// Type alias for extracting the edge color in a [`TransitionSystem`].
pub type EdgeColor<X> = <X as TransitionSystem>::EdgeColor;
/// Type alias for extracting the state index in a [`TransitionSystem`].
pub type StateIndex<X = DTS> = <X as TransitionSystem>::StateIndex;
/// Type alias for a tuple representing an edge in a [`TransitionSystem`].
pub type EdgeTuple<Ts> = (
    StateIndex<Ts>,
    EdgeExpression<Ts>,
    EdgeColor<Ts>,
    StateIndex<Ts>,
);
/// Type alias for the reference to an edge of a given [`TransitionSystem`], which is what its
/// [`TransitionSystem::edges_from`] yields.
pub type EdgeOf<'a, T> =
    EdgeRef<'a, StateIndex<T>, EdgeExpression<T>, <T as TransitionSystem>::EdgeColor>;

/// Implementors of this trait have a distinguished (initial) state.
pub trait Pointed: TransitionSystem {
    /// Returns the index of the initial state.
    fn initial(&self) -> Self::StateIndex;

    /// Returns the color of the initial state.
    fn initial_color(&self) -> Self::StateColor {
        self.state_color(self.initial())
            .expect("Initial state must exist and be colored!")
            .into_owned()
    }

    /// Explores the states that are reachable from the initial state and returns them as a
    /// finite transition system, see [`operations::ReachablePart`]. This is how an implicit
    /// system like a subset construction or a product is turned into something that can be
    /// collected or analysed as a whole.
    fn reachable_part(self) -> operations::ReachablePart<Self> {
        operations::ReachablePart::new(self)
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

use self::operations::ProvidesStateColor;

#[cfg(test)]
mod tests {
    use crate::TransitionSystem;

    #[test]
    fn linked_list_ts_answers_none_for_unknown_states() {
        use crate::DTS;
        use crate::Void;
        use crate::alphabet::CharAlphabet;
        use crate::ts::{ForAlphabet, Sproutable};

        let mut ts: DTS<CharAlphabet, bool, Void> = DTS::for_alphabet(CharAlphabet::of_size(2));
        let q = ts.add_state(true);
        let p = ts.add_state(false);
        assert!(ts.edges_from(q).is_some());
        assert_eq!(ts.state_color(p).as_deref(), Some(&false));
        assert!(ts.edges_from(17).is_none());
        assert_eq!(ts.state_color(17), None);
        // a removed state no longer exists
        use crate::ts::Shrinkable;
        ts.remove_state(p);
        assert!(ts.edges_from(p).is_none());
        assert_eq!(ts.state_color(p), None);
        assert!(ts.edges_from(q).is_some());
    }

    #[test]
    fn adapters_forward_state_membership() {
        use crate::States;
        use crate::ts::{Deterministic, Pointed};

        let dfa = crate::tests::wiki_dfa();
        let n = dfa.state_count();
        assert!(dfa.contains_state(0));
        assert!(!dfa.contains_state(n as u32 + 5));

        let erased = (&dfa).erase_state_colors();
        assert_eq!(erased.state_count(), n);
        assert!(erased.contains_state(0));
        assert!(!erased.contains_state(n as u32 + 5));

        let restricted = (&dfa).restrict_state_indices(|q| q != 0);
        assert!(!restricted.contains_state(0));
        assert!(restricted.contains_state(1));
        assert_eq!(restricted.state_count(), n - 1);

        let finite = dfa
            .ts()
            .clone()
            .with_initial(0)
            .subset_construction()
            .reachable_part();
        assert!(finite.contains_state(0));
        assert!(!finite.contains_state(finite.state_count() + 5));
        assert!(finite.successor(0, 'a').is_some());
        assert!(finite.successor(finite.state_count() + 5, 'a').is_none());
        assert_eq!(finite.initial(), 0);
    }

    #[test]
    fn transitions_from_unknown_state_is_none() {
        let dfa = crate::tests::wiki_dfa();
        assert!(dfa.transitions_from(0).is_some());
        assert!(dfa.transitions_from(100).is_none());
    }
}
