use itertools::Itertools;
use tracing::debug;

use crate::{
    math::{Map, Set},
    prelude::*,
    transition_system::{EdgeReference, EdgeTuple},
};
use std::{
    fmt::{Debug, Display},
    hash::Hash,
    mem::ManuallyDrop,
    ops::Deref,
};

use self::alphabet::Matcher;

pub type EdgeListsNondeterministic<A, Q, C> = EdgeLists<A, Q, C, false>;
pub type EdgeListsDeterministic<A, Q, C> = EdgeLists<A, Q, C, true>;

/// An implementation of a transition system with states of type `Q` and colors of type `C`. It stores
/// the states and edges in a vector, which allows for fast access and iteration. The states and edges
/// are indexed by their position in the respective vector.
#[derive(Clone, PartialEq, Eq)]
pub struct EdgeLists<A: Alphabet, Q = crate::Void, C = crate::Void, const DET: bool = true> {
    pub(crate) alphabet: A,
    pub(crate) states: Map<usize, MutableTsState<A, Q, C>>,
}

/// Type alias that takes a [`TransitionSystem`] and gives the type of a corresponding [`MutableTs`], i.e. one
/// with the same alphabet, edge and state colors.
pub type IntoEdgeLists<Ts, const DET: bool = true> = EdgeLists<
    <Ts as TransitionSystem>::Alphabet,
    <Ts as TransitionSystem>::StateColor,
    <Ts as TransitionSystem>::EdgeColor,
    DET,
>;

impl<A: Alphabet, C: Color, Q: Color, const DET: bool> EdgeLists<A, Q, C, DET> {
    /// Creates a new transition system with the given alphabet.
    pub fn new(alphabet: A) -> Self {
        Self {
            alphabet,
            states: Map::default(),
        }
    }
    /// Creates a new transition system with the given alphabet.
    pub fn size_hint(alphabet: A, size: usize) -> Self {
        Self {
            alphabet,
            states: Map::with_capacity(size),
        }
    }

    pub fn into_deterministic(self) -> EdgeListsDeterministic<A, Q, C> {
        match self.try_into_deterministic() {
            Ok(ts) => ts,
            Err(ts) => {
                tracing::error!("Tried to convert non-deterministic transition system to deterministic one\n{:?}", ts);
                panic!("This transition system is not deterministic");
            }
        }
    }

    pub fn try_into_deterministic(self) -> Result<EdgeListsDeterministic<A, Q, C>, Self> {
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
        state: impl Indexes<Self>,
        pred: F,
    ) -> Option<Vec<EdgeTuple<Self>>>
    where
        F: FnMut(&MutableTsOutEdge<A, C>) -> bool,
    {
        let q = state.to_index(self)?;
        Some(ExtractEdgeTuplesFrom::new(self.states.get_mut(&q)?, pred).collect())
    }

    pub fn extract_edge_tuples<F>(&mut self, pred: F) -> Vec<EdgeTuple<Self>>
    where
        F: FnMut(usize, &MutableTsOutEdge<A, C>) -> bool,
    {
        ExtractAllEdgeTuples::new(self, pred).collect()
    }

    pub(crate) fn mutablets_remove_state(&mut self, usize: usize) -> Option<Q> {
        let state = self.states.swap_remove(&usize)?;
        self.states
            .iter_mut()
            .for_each(|(_, s)| s.remove_outgoing_edges_to(usize));
        Some(state.color)
    }

    /// Creates a `MutableTs` from the given alphabet and states.
    pub(crate) fn from_parts(alphabet: A, states: Map<usize, MutableTsState<A, Q, C>>) -> Self {
        Self { alphabet, states }
    }

    /// Decomposes the `MutableTs` into its constituent parts.
    #[allow(clippy::type_complexity)]
    pub(crate) fn into_parts(self) -> (A, Map<usize, MutableTsState<A, Q, C>>) {
        (self.alphabet, self.states)
    }

    /// Creates an empty `MutableTs` ensuring the given capacity.
    pub fn with_capacity(alphabet: A, states: usize) -> Self {
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
    pub fn raw_state_map(&self) -> &Map<usize, MutableTsState<A, Q, C>> {
        &self.states
    }

    /// Attempts to find the index of a state with the given `color`. If no such state is
    /// found, `None` is returned. Note, that the function simply returns the first state
    /// with the given color. As the order in which the states are stored is not guaranteed,
    /// subsequent calls may lead to different results, if two states with the same color
    /// exist.
    #[inline(always)]
    pub fn find_by_color(&self, color: &Q) -> Option<usize>
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
    pub fn indices_with_color(&self) -> impl Iterator<Item = (usize, &StateColor<Self>)> {
        self.states
            .iter()
            .map(|(usize, state)| (*usize, state.color()))
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> crate::transition_system::Shrinkable
    for EdgeLists<A, Q, C, DET>
{
    fn remove_state<Idx: Indexes<Self>>(&mut self, state: Idx) -> Option<Q> {
        self.mutablets_remove_state(state.to_index(self)?)
    }
    fn remove_edges_from_matching(
        &mut self,
        source: impl Indexes<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let q = source.to_index(self)?;
        self.extract_edge_tuples_for(q, |(e, c, p)| matcher.matches(e))
    }

    fn remove_edges_between_matching(
        &mut self,
        source: impl Indexes<Self>,
        target: impl Indexes<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let source = source.to_index(self)?;
        let target = target.to_index(self)?;
        self.extract_edge_tuples_for(source, |(e, c, p)| matcher.matches(e) && target.eq(p))
    }

    fn remove_edges_between(
        &mut self,
        source: impl Indexes<Self>,
        target: impl Indexes<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let source = source.to_index(self)?;
        let target = target.to_index(self)?;
        self.extract_edge_tuples_for(source, |(e, c, p)| target.eq(p))
    }

    fn remove_edges_from(
        &mut self,
        source: impl Indexes<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let q = source.to_index(self)?;
        self.extract_edge_tuples_for(q, |_| true)
    }

    fn remove_edges_to(&mut self, target: impl Indexes<Self>) -> Option<Vec<EdgeTuple<Self>>> {
        let p = target.to_index(self)?;
        if !self.states.contains_key(&p) {
            return None;
        }
        Some(self.extract_edge_tuples(|_, (_, _, q)| *q == p))
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> EdgeLists<A, Q, C, DET> {
    /// Returns an iterator over the [`EdgeIndex`]es of the edges leaving the given state.
    pub(crate) fn mutablets_edges_from(
        &self,
        source: usize,
    ) -> Option<impl Iterator<Item = &'_ (A::Expression, C, usize)> + '_> {
        self.states.get(&source).map(|s| s.edges.iter())
    }

    /// Checks whether the state exists.
    pub fn contains_state<I: Into<usize>>(&self, index: I) -> bool {
        self.states.contains_key(&index.into())
    }
}

/// A state in a transition system. This stores the color of the state and the index of the
/// first edge leaving the state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct MutableTsState<A: Alphabet, Q, C> {
    id: usize,
    color: Q,
    edges: Vec<(A::Expression, C, usize)>,
}

impl<A: Alphabet, Q: Color, C: Color> MutableTsState<A, Q, C> {
    pub fn new_with_intial_id(color: Q) -> Self {
        Self {
            id: 0,
            color,
            edges: Default::default(),
        }
    }

    /// Creates a new state with the given color.
    pub fn new(id: usize, color: Q) -> Self {
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
        to: usize,
    ) -> Option<(usize, A::Expression, C, usize)> {
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

    pub fn remove_outgoing_edges_to(&mut self, target: usize) {
        self.edges.retain(|(_e, _c, q)| *q != target);
    }

    pub fn edges(&self) -> std::slice::Iter<'_, (A::Expression, C, usize)> {
        self.edges.iter()
    }

    pub fn edge_map(&self) -> &[(A::Expression, C, usize)] {
        &self.edges
    }

    pub fn add_edge(
        &mut self,
        on: A::Expression,
        color: C,
        to: usize,
    ) -> EdgeReference<'_, A::Expression, usize, C> {
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

    pub fn recolor<P: Color>(self, color: P) -> MutableTsState<A, P, C> {
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

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> TransitionSystem
    for EdgeLists<A, Q, C, DET>
{
    type StateColor = Q;
    type EdgeColor = C;
    type StateIndex = usize;
    type EdgeRef<'this> = EdgeReference<'this, A::Expression, usize, C> where Self: 'this;
    type StateIndices<'this> = std::iter::Cloned<indexmap::map::Keys<'this, usize, MutableTsState<A, Q, C>>> where Self: 'this;

    type Alphabet = A;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }
    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.states.keys().cloned()
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        let state = state.to_index(self)?;
        self.raw_state_map().get(&state).map(|s| s.color().clone())
    }

    fn edges_from<X: Indexes<Self>>(&self, state: X) -> Option<Self::EdgesFromIter<'_>> {
        let q = state.to_index(self)?;
        if !self.contains_state(q) {
            return None;
        }
        Some(EdgesFrom::new(q, self.states.get(&q).unwrap().edges.iter()))
    }
    type EdgesFromIter<'this> = EdgesFrom<'this, A::Expression, C> where Self: 'this;
}

impl<Q, C, const DET: bool> EdgeLists<CharAlphabet, Q, C, DET> {
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
pub struct EdgesFrom<'ts, E, C> {
    edges: std::slice::Iter<'ts, (E, C, usize)>,
    source: usize,
}

impl<'ts, E, C> EdgesFrom<'ts, E, C> {
    /// Creates a new instance from the given components.
    pub fn new(source: usize, edges: std::slice::Iter<'ts, (E, C, usize)>) -> Self {
        Self { edges, source }
    }
}

impl<'ts, E, C> Iterator for EdgesFrom<'ts, E, C> {
    type Item = EdgeReference<'ts, E, usize, C>;

    fn next(&mut self) -> Option<Self::Item> {
        self.edges
            .next()
            .map(|(e, c, q)| EdgeReference::new(self.source, e, c, *q))
    }
}

impl<A, C, Q, const DET: bool> std::fmt::Debug for EdgeLists<A, Q, C, DET>
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
                "q{}[{:?}] {}",
                i,
                state.color,
                state
                    .edges()
                    .map(|(e, c, p)| format!("{}:{:?}->{}", e.show(), c, p))
                    .join(", ")
            )?;
        }
        Ok(())
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> Sproutable for EdgeLists<A, Q, C, DET> {
    /// Adds a state with given `color` to the transition system, returning the index of
    /// the new state.
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        let id = self.states.len();
        let state = MutableTsState::new(id, color);
        self.states.insert(id, state);
        id
    }

    fn add_edge<E>(&mut self, t: E) -> Option<Self::EdgeRef<'_>>
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
            "Source {} or target {} vertex does not exist in the graph.",
            q.show(),
            p.show()
        );

        Some(self.states.get_mut(&q)?.add_edge(a, c, p))
    }

    fn set_state_color<Idx: Indexes<Self>, X: Into<StateColor<Self>>>(
        &mut self,
        index: Idx,
        color: X,
    ) {
        let Some(index) = index.to_index(self) else {
            tracing::error!("cannot set color of state that does not exist");
            return;
        };
        self.states
            .get_mut(&index)
            .expect("State must exist")
            .set_color(color.into());
    }
}

type MutableTsOutEdge<A, C> = (<A as Alphabet>::Expression, C, usize);

/// An iterator which uses a closure to determine if an element should be removed.
/// This is used for extracting elements from a `Vec` while mutating it in place.
///
/// Pretty much stolen from the standard library's [`Vec::extract_if`], but since that
/// is still unstable and we need something slightly different, we just implement our own.
///
/// See the [`MutableTs::extract_edge_tuples`] method for an example of usage.
#[derive(Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ExtractEdgeTuplesFrom<'a, A: Alphabet, Q, C, F>
where
    F: FnMut(&MutableTsOutEdge<A, C>) -> bool,
{
    pub(super) state: &'a mut MutableTsState<A, Q, C>,
    /// The index of the item that will be inspected by the next call to `next`.
    pub(super) usize: usize,
    /// The number of items that have been drained (removed) thus far.
    pub(super) del: usize,
    /// The original length of `vec` prior to draining.
    pub(super) old_len: usize,
    /// The filter test predicate.
    pub(super) pred: F,
}

impl<'a, A: Alphabet, Q, C, F> ExtractEdgeTuplesFrom<'a, A, Q, C, F>
where
    F: FnMut(&MutableTsOutEdge<A, C>) -> bool,
{
    pub fn new(
        state: &'a mut MutableTsState<A, Q, C>,
        pred: F,
    ) -> ExtractEdgeTuplesFrom<'a, A, Q, C, F> {
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

impl<'a, A: Alphabet, Q, C, F> Iterator for ExtractEdgeTuplesFrom<'a, A, Q, C, F>
where
    F: FnMut(&MutableTsOutEdge<A, C>) -> bool,
{
    type Item = (usize, A::Expression, C, usize);

    fn next(&mut self) -> Option<(usize, A::Expression, C, usize)> {
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
                    let src: *const MutableTsOutEdge<A, C> = &v[i];
                    let dst: *mut MutableTsOutEdge<A, C> = &mut v[i - del];
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

impl<'a, A: Alphabet, Q, C, F> Drop for ExtractEdgeTuplesFrom<'a, A, Q, C, F>
where
    F: FnMut(&MutableTsOutEdge<A, C>) -> bool,
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
pub struct ExtractAllEdgeTuples<'a, A: Alphabet, Q, C, F>
where
    F: FnMut(usize, &MutableTsOutEdge<A, C>) -> bool,
{
    pub(super) state: Option<&'a mut MutableTsState<A, Q, C>>,
    /// The index of the item that will be inspected by the next call to `next`.
    pub(super) usize: usize,
    /// The number of items that have been drained (removed) thus far.
    pub(super) del: usize,
    /// The original length of `vec` prior to draining.
    pub(super) old_len: usize,
    /// The filter test predicate.
    pub(super) pred: F,
    pub(super) remaining: indexmap::map::ValuesMut<'a, usize, MutableTsState<A, Q, C>>,
}

impl<'a, A: Alphabet, Q, C, F> ExtractAllEdgeTuples<'a, A, Q, C, F>
where
    F: FnMut(usize, &MutableTsOutEdge<A, C>) -> bool,
{
    pub fn new<const DET: bool>(ts: &'a mut EdgeLists<A, Q, C, DET>, pred: F) -> Self {
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

impl<'a, A: Alphabet, Q, C, F> Iterator for ExtractAllEdgeTuples<'a, A, Q, C, F>
where
    F: FnMut(usize, &MutableTsOutEdge<A, C>) -> bool,
{
    type Item = (usize, A::Expression, C, usize);

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
                        let src: *const MutableTsOutEdge<A, C> = &v[i];
                        let dst: *mut MutableTsOutEdge<A, C> = &mut v[i - del];
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

impl<'a, A: Alphabet, Q, C, F> Drop for ExtractAllEdgeTuples<'a, A, Q, C, F>
where
    F: FnMut(usize, &MutableTsOutEdge<A, C>) -> bool,
{
    fn drop(&mut self) {
        debug!("Not really sure how to handle dropping of ExtractAllEdgeTuples. Basically all the drop method is called for each ExtractEdgeTuplesFrom, so we should probably be fine. Or not. Who knows.");
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> PredecessorIterable
    for EdgeLists<A, Q, C, DET>
{
    type PreEdgeRef<'this> = EdgeReference<'this, A::Expression, usize, C> where Self: 'this;
    type EdgesToIter<'this> = EdgeListsPredecessors<'this, A, Q, C, DET>
    where
        Self: 'this;
    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        let target = state.to_index(self)?;
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
pub struct EdgeListsPredecessors<'a, A: Alphabet, Q: Color, C: Color, const DET: bool> {
    idx: Option<usize>,
    inner_pos: usize,
    target: usize,
    it: indexmap::map::Keys<'a, usize, MutableTsState<A, Q, C>>,
    elp: &'a EdgeLists<A, Q, C, DET>,
}

impl<'a, A: Alphabet, Q: Color, C: Color, const DET: bool> Iterator
    for EdgeListsPredecessors<'a, A, Q, C, DET>
{
    type Item = EdgeReference<'a, A::Expression, usize, C>;

    fn next(&mut self) -> Option<Self::Item> {
        'outer: loop {
            let q = self.idx?;
            let Some(state) = self.elp.states.get(&q) else {
                panic!("State with index {} does not exist", q);
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

fn recast<A: Alphabet, Q: Color, C: Color, const DET: bool, const OUT_DET: bool>(
    ts: EdgeLists<A, Q, C, DET>,
) -> EdgeLists<A, Q, C, OUT_DET> {
    if !DET && OUT_DET && !ts.is_deterministic() {
        panic!("cannot convert non-deterministic transition system to deterministic");
    }
    let EdgeLists { alphabet, states } = ts;
    EdgeLists { alphabet, states }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> ForAlphabet<A> for EdgeLists<A, Q, C, DET> {
    fn for_alphabet(from: A) -> Self {
        Self::new(from)
    }
    fn for_alphabet_size_hint(from: A, _size_hint: (usize, usize)) -> Self {
        Self::size_hint(from, _size_hint.0)
    }
}
