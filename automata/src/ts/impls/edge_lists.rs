use itertools::Itertools;
use tracing::debug;

use crate::core::{
    alphabet::{Alphabet, CharAlphabet, Expression, Matcher},
    math,
    math::Map,
    Color, Show, Void,
};
use crate::transition_system::predecessors::PredecessorIterable;
use crate::transition_system::{
    Deterministic, EdgeColor, EdgeExpression, EdgeReference, EdgeTuple, ForAlphabet, IndexType,
    IntoEdgeTuple, IsEdge, ScalarIndexType, Sproutable, StateColor, StateIndex, TSBuilder,
};
use crate::TransitionSystem;
use std::{
    borrow::Borrow,
    collections::{BTreeMap, BTreeSet},
    fmt::{Debug, Display},
    hash::Hash,
    mem::ManuallyDrop,
    ops::Deref,
};

use super::DefaultIdType;

pub type EdgeListsNondeterministic<A, Q, C, IdType = DefaultIdType> =
    EdgeLists<A, Q, C, false, IdType>;
pub type EdgeListsDeterministic<A, Q, C, IdType = DefaultIdType> = EdgeLists<A, Q, C, true, IdType>;

/// An implementation of a transition system with states of type `Q` and colors of type `C`. It stores
/// the states and edges in a vector, which allows for fast access and iteration. The states and edges
/// are indexed by their position in the respective vector.
#[derive(Clone, PartialEq, Eq)]
pub struct EdgeLists<
    A: Alphabet,
    Q = Void,
    C = Void,
    const DET: bool = true,
    IdType: ScalarIndexType = DefaultIdType,
> {
    pub(crate) alphabet: A,
    pub(crate) states: Map<IdType, MutableTsState<A, Q, C, IdType>>,
}

/// type alias that takes a [`TransitionSystem`] and gives the type of a corresponding [`MutableTs`], i.e. one
/// with the same alphabet, edge and state colors.
pub type IntoEdgeLists<Ts, const DET: bool = true, IdType = DefaultIdType> = EdgeLists<
    <Ts as TransitionSystem>::Alphabet,
    <Ts as TransitionSystem>::StateColor,
    <Ts as TransitionSystem>::EdgeColor,
    DET,
    IdType,
>;

impl<A: Alphabet, C: Color, Q: Color, const DET: bool, IdType: ScalarIndexType>
    EdgeLists<A, Q, C, DET, IdType>
{
    /// Creates a new transition system with the given alphabet.
    pub fn new(alphabet: A) -> Self {
        Self {
            alphabet,
            states: Map::default(),
        }
    }

    pub fn into_deterministic(self) -> EdgeListsDeterministic<A, Q, C, IdType> {
        match self.try_into_deterministic() {
            Ok(ts) => ts,
            Err(ts) => {
                tracing::error!("Tried to convert non-deterministic transition system to deterministic one\n{:?}", ts);
                panic!("This transition system is not deterministic");
            }
        }
    }

    pub fn try_into_deterministic(self) -> Result<EdgeListsDeterministic<A, Q, C, IdType>, Self> {
        if DET {
            if !self.is_deterministic() {
                tracing::error!("Tried to convert non-deterministic transition system to deterministic one\n{:?}", self);
                panic!("This transition system is not deterministic");
            }
            Ok(recast(self))
        } else if self.is_deterministic() {
            Ok(recast(self))
        } else {
            Err(self)
        }
    }

    pub fn extract_edge_tuples_for<F>(
        &mut self,
        q: StateIndex<Self>,
        pred: F,
    ) -> Option<Vec<EdgeTuple<Self>>>
    where
        F: FnMut(&EdgeListsOutEdge<A, C, IdType>) -> bool,
    {
        Some(ExtractEdgeTuplesFrom::new(self.states.get_mut(&q)?, pred).collect())
    }

    pub fn extract_edge_tuples<F>(&mut self, pred: F) -> Vec<EdgeTuple<Self>>
    where
        F: FnMut(IdType, &EdgeListsOutEdge<A, C, IdType>) -> bool,
    {
        ExtractAllEdgeTuples::new(self, pred).collect()
    }

    pub(crate) fn mutablets_remove_state(&mut self, q: IdType) -> Option<Q> {
        let state = self.states.swap_remove(&q)?;
        self.states
            .iter_mut()
            .for_each(|(_, s)| s.remove_outgoing_edges_to(q));
        Some(state.color)
    }

    /// Creates a `MutableTs` from the given alphabet and states.
    pub(crate) fn from_parts(
        alphabet: A,
        states: Map<IdType, MutableTsState<A, Q, C, IdType>>,
    ) -> Self {
        Self { alphabet, states }
    }

    /// Decomposes the `MutableTs` into its constituent parts.
    #[allow(clippy::type_complexity)]
    pub(crate) fn into_parts(self) -> (A, Map<IdType, MutableTsState<A, Q, C, IdType>>) {
        (self.alphabet, self.states)
    }

    /// Creates an empty `MutableTs` ensuring the given capacity.
    pub fn with_capacity(alphabet: A, states: usize) -> Self
    where
        StateColor<Self>: Default,
        IdType: From<usize> + IndexType,
    {
        Self {
            alphabet,
            states: Map::with_capacity(states),
        }
    }

    /// Gets a mutable reference to the alphabet of the transition system.
    pub fn alphabet(&self) -> &A {
        &self.alphabet
    }

    /// Returns a reference to the underlying statemap.
    pub fn raw_state_map(&self) -> &Map<IdType, MutableTsState<A, Q, C, IdType>> {
        &self.states
    }

    /// Attempts to find the index of a state with the given `color`. If no such state is
    /// found, `None` is returned. Note, that the function simply returns the first state
    /// with the given color. As the order in which the states are stored is not guaranteed,
    /// subsequent calls may lead to different results, if two states with the same color
    /// exist.
    #[inline(always)]
    pub fn find_by_color(&self, color: &Q) -> Option<IdType>
    where
        Q: Eq,
    {
        self.states.iter().find_map(|(usize, state)| {
            if state.color() == color {
                Some(*usize)
            } else {
                None
            }
        })
    }

    /// Returns an iterator emitting pairs of state indices and their colors.
    pub fn indices_with_color(&self) -> impl Iterator<Item = (IdType, &StateColor<Self>)> {
        self.states
            .iter()
            .map(|(usize, state)| (*usize, state.color()))
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, IdType: ScalarIndexType>
    crate::transition_system::Shrinkable for EdgeLists<A, Q, C, DET, IdType>
{
    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<Q> {
        self.mutablets_remove_state(state)
    }
    fn remove_edges_from_matching(
        &mut self,
        q: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        self.extract_edge_tuples_for(q, |(e, c, p)| matcher.matches(e))
    }

    fn remove_edges_between_matching(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        self.extract_edge_tuples_for(source, |(e, c, p)| matcher.matches(e) && target.eq(p))
    }

    fn remove_edges_between(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        self.extract_edge_tuples_for(source, |(e, c, p)| target.eq(p))
    }

    fn remove_edges_from(
        &mut self,
        q: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        self.extract_edge_tuples_for(q, |_| true)
    }

    fn remove_edges_to(&mut self, target: StateIndex<Self>) -> Option<Vec<EdgeTuple<Self>>> {
        if !self.states.contains_key(&target) {
            return None;
        }
        Some(self.extract_edge_tuples(|_, (_, _, q)| *q == target))
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, IdType: ScalarIndexType>
    EdgeLists<A, Q, C, DET, IdType>
{
    /// Returns an iterator over the [`EdgeIndex`]es of the edges leaving the given state.
    pub(crate) fn mutablets_edges_from(
        &self,
        source: IdType,
    ) -> Option<impl Iterator<Item = &'_ (A::Expression, C, IdType)> + '_> {
        self.states.get(&source).map(|s| s.edges.iter())
    }

    /// Checks whether the state exists.
    pub fn contains_state<I: Into<IdType>>(&self, index: I) -> bool {
        self.states.contains_key(&index.into())
    }
}

impl<A: Alphabet, Q: Color, C: Hash + Debug + Eq + Clone> Deterministic for EdgeLists<A, Q, C> {
    fn edge(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Self::EdgeRef<'_>> {
        let mut it = self.edges_matching(state, matcher)?;
        let out = Some(it.next()?);
        debug_assert!(
            it.next().is_none(),
            "Not deterministic, {state} has mutliple edges on the same expression!"
        );
        out
    }
}

/// A state in a transition system. This stores the color of the state and the index of the
/// first edge leaving the state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct MutableTsState<A: Alphabet, Q, C, IdType: ScalarIndexType = DefaultIdType> {
    id: IdType,
    color: Q,
    edges: Vec<(A::Expression, C, IdType)>,
}

impl<A: Alphabet, Q: Color, C: Color, IdType: ScalarIndexType> MutableTsState<A, Q, C, IdType> {
    pub fn new_with_intial_id(color: Q) -> Self {
        Self {
            id: IdType::from_usize(0),
            color,
            edges: Default::default(),
        }
    }

    /// Creates a new state with the given color.
    pub fn new(id: IdType, color: Q) -> Self {
        Self {
            id,
            color,
            edges: Default::default(),
        }
    }

    pub fn set_color(&mut self, color: Q) {
        self.color = color;
    }

    pub(crate) fn remove_edge(
        &mut self,
        on: &A::Expression,
        color: &C,
        to: IdType,
    ) -> Option<(IdType, A::Expression, C, IdType)> {
        if let Some(position) = self
            .edges
            .iter()
            .position(|(e, c, q)| *q == to && e == on && c == color)
        {
            let (e, c, q) = self.edges.remove(position);
            Some((self.id, e, c, q))
        } else {
            None
        }
    }

    pub fn remove_outgoing_edges_to(&mut self, target: IdType) {
        self.edges.retain(|(_e, _c, q)| *q != target);
    }

    pub fn edges(&self) -> std::slice::Iter<'_, (A::Expression, C, IdType)> {
        self.edges.iter()
    }

    pub fn edge_map(&self) -> &[(A::Expression, C, IdType)] {
        &self.edges
    }

    pub fn add_edge(
        &mut self,
        on: A::Expression,
        color: C,
        to: IdType,
    ) -> EdgeReference<'_, A::Expression, IdType, C> {
        debug_assert!(
            !self
                .edges
                .iter()
                .any(|(e, c, q)| e == &on && c == &color && *q == to),
            "Cannot add edge that already exists."
        );

        self.edges.push((on, color, to));
        let (e, c, q) = self.edges.last().expect("We just added an element!");

        EdgeReference::new(self.id, e, c, *q)
    }

    pub fn recolor<P: Color>(self, color: P) -> MutableTsState<A, P, C, IdType> {
        MutableTsState {
            id: self.id,
            color,
            edges: self.edges,
        }
    }

    /// Obtains a reference to the color of the state.
    pub fn color(&self) -> &Q {
        &self.color
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, IdType: ScalarIndexType> TransitionSystem
    for EdgeLists<A, Q, C, DET, IdType>
{
    type StateColor = Q;
    type EdgeColor = C;
    type StateIndex = IdType;
    type EdgeRef<'this> = EdgeReference<'this, A::Expression, IdType, C> where Self: 'this;
    type StateIndices<'this> = std::iter::Cloned<math::map::Keys<'this, IdType, MutableTsState<A, Q, C, IdType>>> where Self: 'this;

    type Alphabet = A;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }
    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.states.keys().cloned()
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.raw_state_map().get(&state).map(|s| s.color().clone())
    }

    fn edges_from(&self, q: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        if !self.contains_state(q) {
            return None;
        }
        Some(EdgesFrom::new(q, self.states.get(&q).unwrap().edges.iter()))
    }
    type EdgesFromIter<'this> = EdgesFrom<'this, A::Expression, C, IdType> where Self: 'this;
}

impl<Q, C, const DET: bool, IdType: ScalarIndexType> EdgeLists<CharAlphabet, Q, C, DET, IdType> {
    /// Returns a transition system builder for a non-deterministic transition system. This should be the main method for the
    /// construction of non-deterministic transition systems on the fly.
    ///
    /// # Example
    ///
    /// We want to create a DFA with two states 0 and 1 over the alphabet `['a', 'b']`. We want to add the following transitions:
    /// - From state 0 to state 0 on symbol 'a'
    /// - From state 0 to state 1 on symbol 'b'
    /// - From state 1 to state 1 on symbol 'a'
    /// - From state 1 to state 0 on symbol 'b'
    /// Further, state 0 should be initial and colored `true` and state 1 should be colored `false`. This can be done as follows
    /// ```
    /// use automata::prelude::*;
    ///
    /// let ts = TSBuilder::default()
    ///     .with_state_colors([true, false]) // colors given in the order of the states
    ///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 0)])
    ///     .into_dfa(0); // 0 is the initial state
    /// ```
    pub fn builder() -> TSBuilder<Q, C> {
        TSBuilder::default()
    }
}

/// Specialized iterator over the edges that leave a given state in a [`MutableTs`].
pub struct EdgesFrom<'ts, E, C, IdType: ScalarIndexType> {
    edges: std::slice::Iter<'ts, (E, C, IdType)>,
    source: IdType,
}

impl<'ts, E, C, IdType: ScalarIndexType> EdgesFrom<'ts, E, C, IdType> {
    /// Creates a new instance from the given components.
    pub fn new(source: IdType, edges: std::slice::Iter<'ts, (E, C, IdType)>) -> Self {
        Self { edges, source }
    }
}

impl<'ts, E, C, IdType: ScalarIndexType> Iterator for EdgesFrom<'ts, E, C, IdType> {
    type Item = EdgeReference<'ts, E, IdType, C>;

    fn next(&mut self) -> Option<Self::Item> {
        self.edges
            .next()
            .map(|(e, c, q)| EdgeReference::new(self.source, e, c, *q))
    }
}

impl<A, C, Q, const DET: bool, IdType: ScalarIndexType> std::fmt::Debug
    for EdgeLists<A, Q, C, DET, IdType>
where
    A: Alphabet,
    C: Color,
    Q: Color,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Alphabet: {:?}", self.alphabet())?;
        for (i, state) in self.states.iter() {
            writeln!(
                f,
                "q{i:?}[{:?}] {}",
                state.color,
                state
                    .edges()
                    .map(|(e, c, p)| format!("{}:{:?}->{p:?}", e.show(), c))
                    .join(", ")
            )?;
        }
        Ok(())
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, IdType: ScalarIndexType> Sproutable
    for EdgeLists<A, Q, C, DET, IdType>
{
    /// Adds a state with given `color` to the transition system, returning the index of
    /// the new state.
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        let id = IdType::from_usize(self.states.len());
        let state = MutableTsState::new(id, color);
        self.states.insert(id, state);
        id
    }

    fn add_edge<E>(&mut self, t: E) -> Option<EdgeTuple<Self>>
    where
        E: IntoEdgeTuple<Self>,
    {
        let (q, a, c, p) = t.into_edge_tuple();

        if DET
            && self
                .edges_from(q)
                .unwrap()
                .any(|e| e.expression().overlaps(&a))
        {
            return None;
        }

        assert!(
            self.contains_state(q) && self.contains_state(p),
            "Source {q:?} or target {p:?} vertex does not exist in the graph.",
        );

        todo!()
        // Some(self.states.get_mut(&q)?.add_edge(a, c, p))
    }
    fn set_state_color(&mut self, index: StateIndex<Self>, color: StateColor<Self>) {
        self.states
            .get_mut(&index)
            .expect("State must exist")
            .set_color(color);
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, IdType: ScalarIndexType> ForAlphabet<A>
    for EdgeLists<A, Q, C, DET, IdType>
{
    fn for_alphabet(from: A) -> Self {
        Self {
            alphabet: from,
            states: Map::default(),
        }
    }
}

type EdgeListsOutEdge<A, C, IdType> = (<A as Alphabet>::Expression, C, IdType);

/// An iterator which uses a closure to determine if an element should be removed.
/// This is used for extracting elements from a `Vec` while mutating it in place.
///
/// Pretty much stolen from the standard library's [`Vec::extract_if`], but since that
/// is still unstable and we need something slightly different, we just implement our own.
///
/// See the [`MutableTs::extract_edge_tuples`] method for an example of usage.
#[derive(Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ExtractEdgeTuplesFrom<'a, A: Alphabet, Q, C, F, IdType: ScalarIndexType>
where
    F: FnMut(&EdgeListsOutEdge<A, C, IdType>) -> bool,
{
    pub(super) state: &'a mut MutableTsState<A, Q, C, IdType>,
    /// The index of the item that will be inspected by the next call to `next`.
    pub(super) usize: usize,
    /// The number of items that have been drained (removed) thus far.
    pub(super) del: usize,
    /// The original length of `vec` prior to draining.
    pub(super) old_len: usize,
    /// The filter test predicate.
    pub(super) pred: F,
}

impl<'a, A: Alphabet, Q, C, F, IdType: ScalarIndexType>
    ExtractEdgeTuplesFrom<'a, A, Q, C, F, IdType>
where
    F: FnMut(&EdgeListsOutEdge<A, C, IdType>) -> bool,
{
    pub fn new(
        state: &'a mut MutableTsState<A, Q, C, IdType>,
        pred: F,
    ) -> ExtractEdgeTuplesFrom<'a, A, Q, C, F, IdType> {
        let old_len = state.edges.len();
        ExtractEdgeTuplesFrom {
            state,
            usize: 0,
            del: 0,
            old_len,
            pred,
        }
    }
}

impl<'a, A: Alphabet, Q, C, F, IdType: ScalarIndexType> Iterator
    for ExtractEdgeTuplesFrom<'a, A, Q, C, F, IdType>
where
    F: FnMut(&EdgeListsOutEdge<A, C, IdType>) -> bool,
{
    type Item = (IdType, A::Expression, C, IdType);

    fn next(&mut self) -> Option<(IdType, A::Expression, C, IdType)> {
        unsafe {
            while self.usize < self.old_len {
                let i = self.usize;
                let v = std::slice::from_raw_parts_mut(self.state.edges.as_mut_ptr(), self.old_len);
                let drained = (self.pred)(&mut v[i]);
                // Update the index *after* the predicate is called. If the index
                // is updated prior and the predicate panics, the element at this
                // index would be leaked.
                self.usize += 1;
                if drained {
                    self.del += 1;
                    let (e, c, p) = std::ptr::read(&v[i]);
                    // piece together into a n edge tuple
                    return Some((self.state.id, e, c, p));
                } else if self.del > 0 {
                    let del = self.del;
                    let src: *const EdgeListsOutEdge<A, C, IdType> = &v[i];
                    let dst: *mut EdgeListsOutEdge<A, C, IdType> = &mut v[i - del];
                    std::ptr::copy_nonoverlapping(src, dst, 1);
                }
            }
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.old_len - self.usize))
    }
}

impl<'a, A: Alphabet, Q, C, F, IdType: ScalarIndexType> Drop
    for ExtractEdgeTuplesFrom<'a, A, Q, C, F, IdType>
where
    F: FnMut(&EdgeListsOutEdge<A, C, IdType>) -> bool,
{
    fn drop(&mut self) {
        unsafe {
            if self.usize < self.old_len && self.del > 0 {
                // This is a pretty messed up state, and there isn't really an
                // obviously right thing to do. We don't want to keep trying
                // to execute `pred`, so we just backshift all the unprocessed
                // elements and tell the vec that they still exist. The backshift
                // is required to prevent a double-drop of the last successfully
                // drained item prior to a panic in the predicate.
                let ptr = self.state.edges.as_mut_ptr();
                let src = ptr.add(self.usize);
                let dst = src.sub(self.del);
                let tail_len = self.old_len - self.usize;
                src.copy_to(dst, tail_len);
            }
            self.state.edges.set_len(self.old_len - self.del);
        }
    }
}

/// Uses the functionality of [`ExtractEdgeTuplesFrom`] to extract all edge tuples from a
/// transition system that match a given predicate.
#[derive(Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ExtractAllEdgeTuples<'a, A: Alphabet, Q, C, F, IdType: ScalarIndexType>
where
    F: FnMut(IdType, &EdgeListsOutEdge<A, C, IdType>) -> bool,
{
    pub(super) state: Option<&'a mut MutableTsState<A, Q, C, IdType>>,
    /// The index of the item that will be inspected by the next call to `next`.
    pub(super) usize: usize,
    /// The number of items that have been drained (removed) thus far.
    pub(super) del: usize,
    /// The original length of `vec` prior to draining.
    pub(super) old_len: usize,
    /// The filter test predicate.
    pub(super) pred: F,
    pub(super) remaining: math::map::ValuesMut<'a, IdType, MutableTsState<A, Q, C, IdType>>,
}

impl<'a, A: Alphabet, Q, C, F, IdType: ScalarIndexType> ExtractAllEdgeTuples<'a, A, Q, C, F, IdType>
where
    F: FnMut(IdType, &EdgeListsOutEdge<A, C, IdType>) -> bool,
{
    pub fn new<const DET: bool>(ts: &'a mut EdgeLists<A, Q, C, DET, IdType>, pred: F) -> Self {
        let mut it = ts.states.values_mut();
        if let Some(state) = it.next() {
            let old_len = state.edges.len();
            Self {
                state: Some(state),
                usize: 0,
                del: 0,
                old_len,
                pred,
                remaining: it,
            }
        } else {
            Self {
                state: None,
                usize: 0,
                del: 0,
                old_len: 0,
                pred,
                remaining: it,
            }
        }
    }
}

impl<'a, A: Alphabet, Q, C, F, IdType: ScalarIndexType> Iterator
    for ExtractAllEdgeTuples<'a, A, Q, C, F, IdType>
where
    F: FnMut(IdType, &EdgeListsOutEdge<A, C, IdType>) -> bool,
{
    type Item = (IdType, A::Expression, C, IdType);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some(mut current_state) = self.state.take() else {
                // no more states to iterate
                return None;
            };

            unsafe {
                while self.usize < self.old_len {
                    let i = self.usize;
                    let v = std::slice::from_raw_parts_mut(
                        current_state.edges.as_mut_ptr(),
                        self.old_len,
                    );
                    let drained = (self.pred)(current_state.id, &mut v[i]);
                    // Update the index *after* the predicate is called. If the index
                    // is updated prior and the predicate panics, the element at this
                    // index would be leaked.
                    self.usize += 1;
                    if drained {
                        self.del += 1;
                        let (e, c, p) = std::ptr::read(&v[i]);
                        let id = current_state.id;
                        // piece together into a n edge tuple
                        self.state = Some(current_state);
                        return Some((id, e, c, p));
                    } else if self.del > 0 {
                        let del = self.del;
                        let src: *const EdgeListsOutEdge<A, C, IdType> = &v[i];
                        let dst: *mut EdgeListsOutEdge<A, C, IdType> = &mut v[i - del];
                        std::ptr::copy_nonoverlapping(src, dst, 1);
                    }
                }
            }

            // current extractor is done, move out predicate and get next one
            self.state = self.remaining.next();
            self.usize = 0;
            self.del = 0;
            self.old_len = self.state.as_ref().map(|s| s.edges.len()).unwrap_or(0);
        }
    }
}

impl<'a, A: Alphabet, Q, C, F, IdType: ScalarIndexType> Drop
    for ExtractAllEdgeTuples<'a, A, Q, C, F, IdType>
where
    F: FnMut(IdType, &EdgeListsOutEdge<A, C, IdType>) -> bool,
{
    fn drop(&mut self) {
        debug!("Not really sure how to handle dropping of ExtractAllEdgeTuples. Basically all the drop method is called for each ExtractEdgeTuplesFrom, so we should probably be fine. Or not. Who knows.");
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, IdType: ScalarIndexType> PredecessorIterable
    for EdgeLists<A, Q, C, DET, IdType>
{
    type PreEdgeRef<'this> = EdgeReference<'this, A::Expression, IdType, C> where Self: 'this;
    type EdgesToIter<'this> = EdgeListsPredecessors<'this, A, Q, C, DET, IdType>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        let target = state;
        let mut it = self.states.keys();
        Some(EdgeListsPredecessors {
            idx: it.next().cloned(),
            inner_pos: 0,
            target,
            it,
            elp: self,
        })
    }
}

/// Iterator over the predecessors of a state in a BTS.
#[derive(Clone)]
pub struct EdgeListsPredecessors<
    'a,
    A: Alphabet,
    Q: Color,
    C: Color,
    const DET: bool,
    IdType: ScalarIndexType,
> {
    idx: Option<IdType>,
    inner_pos: usize,
    target: IdType,
    it: math::map::Keys<'a, IdType, MutableTsState<A, Q, C, IdType>>,
    elp: &'a EdgeLists<A, Q, C, DET, IdType>,
}

impl<'a, A: Alphabet, Q: Color, C: Color, const DET: bool, IdType: ScalarIndexType> Iterator
    for EdgeListsPredecessors<'a, A, Q, C, DET, IdType>
{
    type Item = EdgeReference<'a, A::Expression, IdType, C>;

    fn next(&mut self) -> Option<Self::Item> {
        'outer: loop {
            let q = self.idx?;
            let Some(state) = self.elp.states.get(&q) else {
                panic!("State with index {q:?} does not exist");
            };

            loop {
                let Some((e, c, p)) = state.edges.get(self.inner_pos) else {
                    self.inner_pos = 0;
                    self.idx = self.it.next().cloned();
                    continue 'outer;
                };

                self.inner_pos += 1;
                if *p == self.target {
                    return Some(EdgeReference::new(q, e, c, *p));
                }
            }
        }
    }
}

fn recast<
    A: Alphabet,
    Q: Color,
    C: Color,
    const DET: bool,
    const OUT_DET: bool,
    IdType: ScalarIndexType,
>(
    ts: EdgeLists<A, Q, C, DET, IdType>,
) -> EdgeLists<A, Q, C, OUT_DET, IdType> {
    if !DET && OUT_DET && !ts.is_deterministic() {
        panic!("cannot convert non-deterministic transition system to deterministic");
    }
    let EdgeLists { alphabet, states } = ts;
    EdgeLists { alphabet, states }
}
