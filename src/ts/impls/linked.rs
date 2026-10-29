use crate::ts::States;
use crate::ts::SymbolOf;
use std::borrow::Cow;
use std::{fmt::Debug, hash::Hash};

use crate::ts::{
    Builder, DefaultIdType, DenseId, Deterministic, EdgeColor, EdgeExpression, EdgeId, EdgeOf,
    EdgeTuple, ForAlphabet, IntoEdgeTuple, Shrinkable, Sproutable, StateColor, StateIndex,
};

mod linked_state;
use linked_state::LinkedState;
pub use linked_state::{LinkedEdgesFrom, LinkedEdgesTo};

mod linked_edge;
use crate::TransitionSystem;
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{Det, Linked, Storage};
use crate::{
    Color, Show, Void,
    alphabet::{Alphabet, CharAlphabet, Matcher},
    math,
};
use linked_edge::{LinkedEdge, NONE};
use tracing::{trace, warn};

/// A transition system that stores its states and edges in two vectors and links the edges of each
/// state into lists. It is non-deterministic and works for any [`Alphabet`].
///
/// # Layout
/// Every edge stores its endpoints and the links of the out-list of its source and the in-list of its
/// target as `u32`s, with `u32::MAX` standing for "no edge". That is 24 bytes of bookkeeping per
/// edge. Predecessors are therefore available without a separate index.
///
/// # Stable ids
/// Removing an edge or a state leaves a tombstone instead of moving another element into its slot, so
/// the [`EdgeId`] returned by [`LinkedTs::insert_edge`] and the state indices stay valid. Ids are never
/// reused. The memory of tombstones is only given back by [`LinkedTs::compact`], which returns
/// a [`Compaction`] to translate old ids into new ones. Collecting a transition system into a new one
/// compacts as well.
///
/// Use [`Det<LinkedTs>`](crate::ts::Det) for a deterministic system that replaces overlapping edges.
#[derive(Clone)]
pub struct LinkedTs<A: Alphabet = CharAlphabet, Q = Void, C = Void> {
    alphabet: A,
    states: Vec<LinkedState<Q>>,
    edges: Vec<LinkedEdge<A::Expression, C>>,
    live_edges: usize,
}

/// The renaming of states and edges that [`LinkedTs::compact`] performed.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Compaction {
    states: Vec<Option<DefaultIdType>>,
    edges: Vec<Option<EdgeId>>,
}

impl Compaction {
    /// The new index of the state that had index `old` before compaction, or `None` if that state
    /// had been removed.
    pub fn state(&self, old: DefaultIdType) -> Option<DefaultIdType> {
        self.states.get(old as usize).copied().flatten()
    }

    /// The new id of the edge that had id `old` before compaction, or `None` if that edge had been
    /// removed.
    pub fn edge(&self, old: EdgeId) -> Option<EdgeId> {
        self.edges.get(old.into_usize()).copied().flatten()
    }
}

impl<A: Alphabet, Q: Color, C: Color> LinkedTs<A, Q, C> {
    /// Builds a new empty transition system for the given alphabet with room for `cap` states and
    /// edges.
    pub fn with_capacity(alphabet: A, cap: usize) -> Self {
        Self {
            alphabet,
            states: Vec::with_capacity(cap),
            edges: Vec::with_capacity(cap),
            live_edges: 0,
        }
    }

    /// Pairs the color of every state with its index, so that afterwards the original indices
    /// can be recovered even if states are removed or renumbered.
    pub fn zip_state_indices(self) -> LinkedTs<A, (DefaultIdType, Q), C> {
        LinkedTs {
            alphabet: self.alphabet,
            edges: self.edges,
            live_edges: self.live_edges,
            states: self
                .states
                .into_iter()
                .enumerate()
                .map(|(i, s)| s.map_occupied(|c| (DenseId::from_usize(i), c)))
                .collect(),
        }
    }

    /// Maps the colors of the states with `state_f`, which also gets the index of the state. Compacts
    /// first, so the indices passed to `state_f` and the ids of the result are the ones after
    /// compaction.
    pub fn linked_map_states<QQ: Color, StateF>(self, state_f: StateF) -> LinkedTs<A, QQ, C>
    where
        StateF: Fn(StateIndex<Self>, Q) -> QQ,
    {
        self.linked_map(state_f, |_q, a: <A as Alphabet>::Expression, c, _p| (a, c))
    }

    /// Maps the edges with `edge_f`, which gets source, expression, color and target of an edge and
    /// returns its new expression and color. Compacts first.
    pub fn linked_map_edges<CC: Color, EdgeF>(self, edge_f: EdgeF) -> LinkedTs<A, Q, CC>
    where
        EdgeF: Fn(
            StateIndex<Self>,
            EdgeExpression<Self>,
            EdgeColor<Self>,
            StateIndex<Self>,
        ) -> (EdgeExpression<Self>, CC),
    {
        self.linked_map(|_idx, c| c, edge_f)
    }

    /// Maps states and edges at once, see [`Self::linked_map_states`] and [`Self::linked_map_edges`].
    pub fn linked_map<QQ: Color, CC: Color, StateF, EdgeF>(
        mut self,
        state_f: StateF,
        edge_f: EdgeF,
    ) -> LinkedTs<A, QQ, CC>
    where
        StateF: Fn(StateIndex<Self>, Q) -> QQ,
        EdgeF: Fn(
            StateIndex<Self>,
            EdgeExpression<Self>,
            EdgeColor<Self>,
            StateIndex<Self>,
        ) -> (EdgeExpression<Self>, CC),
    {
        self.compact();
        LinkedTs {
            alphabet: self.alphabet,
            live_edges: self.live_edges,
            states: self
                .states
                .into_iter()
                .enumerate()
                .map(|(i, s)| s.map_occupied(|c| state_f(DenseId::from_usize(i), c)))
                .collect(),
            edges: self.edges.into_iter().map(|e| e.map(&edge_f)).collect(),
        }
    }

    /// The number of edges, tombstones not counted.
    pub fn edge_count(&self) -> usize {
        self.live_edges
    }

    /// One more than the largest [`EdgeId`] that was handed out so far. Use this to size a table
    /// that is indexed by edge ids.
    pub fn edge_bound(&self) -> usize {
        self.edges.len()
    }

    /// Adds the edge `source --expression|color--> target`, without checking whether it overlaps
    /// with an existing edge, and returns its id.
    ///
    /// # Panics
    /// Panics if `source` or `target` is not a state of `self`.
    pub fn insert_edge(
        &mut self,
        source: StateIndex<Self>,
        expression: EdgeExpression<Self>,
        color: EdgeColor<Self>,
        target: StateIndex<Self>,
    ) -> EdgeId {
        assert!(
            self.contains_state(source),
            "cannot add edge from non-existent state {source:?}"
        );
        assert!(
            self.contains_state(target),
            "cannot add edge to non-existent state {target:?}"
        );
        let id = u32::try_from(self.edges.len())
            .ok()
            .filter(|id| *id != NONE)
            .expect("too many edges for 32 bit ids");

        let mut edge = LinkedEdge::new(source, expression, color, target);

        let first_out = self.states[source as usize].first_out_edge();
        if first_out != NONE {
            self.edges[first_out as usize].out_prev = id;
            edge.out_next = first_out;
        }
        self.states[source as usize].set_first_out_edge(id);

        let first_in = self.states[target as usize].first_in_edge();
        if first_in != NONE {
            self.edges[first_in as usize].in_prev = id;
            edge.in_next = first_in;
        }
        self.states[target as usize].set_first_in_edge(id);

        self.edges.push(edge);
        self.live_edges += 1;
        EdgeId(id)
    }

    /// Removes the edge with the given id and returns it. Returns `None` if there is no such edge,
    /// because it was removed already or never existed. The ids of all other edges stay valid.
    pub fn remove_edge(&mut self, id: EdgeId) -> Option<EdgeTuple<Self>> {
        let idx = id.into_usize();
        if !self.edges.get(idx)?.is_live() {
            trace!("tried to remove edge {id} which does not exist");
            return None;
        }
        let LinkedEdge {
            source,
            target,
            out_prev,
            out_next,
            in_prev,
            in_next,
            ..
        } = self.edges[idx];

        if out_prev != NONE {
            self.edges[out_prev as usize].out_next = out_next;
        } else {
            self.states[source as usize].set_first_out_edge(out_next);
        }
        if out_next != NONE {
            self.edges[out_next as usize].out_prev = out_prev;
        }
        if in_prev != NONE {
            self.edges[in_prev as usize].in_next = in_next;
        } else {
            self.states[target as usize].set_first_in_edge(in_next);
        }
        if in_next != NONE {
            self.edges[in_next as usize].in_prev = in_prev;
        }

        let edge = &mut self.edges[idx];
        let removed = (source, edge.expression.clone(), edge.color.clone(), target);
        edge.tombstone();
        self.live_edges -= 1;
        Some(removed)
    }

    /// The edge with the given id, if it exists.
    pub fn edge_by_id(&self, id: EdgeId) -> Option<EdgeOf<'_, Self>> {
        let edge = self.edges.get(id.into_usize())?;
        edge.is_live().then(|| edge.as_edge_ref().with_id(id))
    }

    /// A mutable reference to the color of the edge with the given id, if it exists.
    pub fn edge_color_mut(&mut self, id: EdgeId) -> Option<&mut EdgeColor<Self>> {
        let edge = self.edges.get_mut(id.into_usize())?;
        edge.is_live().then_some(&mut edge.color)
    }

    /// A mutable reference to the color of the given state, if it exists.
    pub fn state_color_mut(&mut self, state: StateIndex<Self>) -> Option<&mut StateColor<Self>> {
        self.states.get_mut(state.into_usize())?.color_mut()
    }

    /// Removes a state and every edge into or out of it, and returns the color of the state. The
    /// indices of the other states stay valid.
    pub(crate) fn linked_remove_state(&mut self, state: StateIndex<Self>) -> Option<Q> {
        if !self.contains_state(state) {
            warn!("tried to remove state {state} which does not exist");
            return None;
        }
        let mut ids = self.out_edge_ids(state, |_| true);
        ids.extend(self.in_edge_ids(state, |_| true));
        // a loop is in both lists
        ids.sort_unstable();
        ids.dedup();
        self.remove_edge_ids(ids);
        debug_assert_eq!(self.states[state as usize].first_out_edge(), NONE);
        debug_assert_eq!(self.states[state as usize].first_in_edge(), NONE);
        self.states[state as usize].vacate()
    }

    /// Removes all edges for which `f` returns `true`, by scanning all of them, and returns
    /// them.
    pub fn filter_remove_edges<F>(&mut self, f: F) -> Vec<EdgeTuple<Self>>
    where
        F: Fn(StateIndex<Self>, &EdgeExpression<Self>, &EdgeColor<Self>, StateIndex<Self>) -> bool,
    {
        let ids: Vec<EdgeId> = self
            .edges
            .iter()
            .enumerate()
            .filter(|(_, e)| e.is_live() && f(e.source, &e.expression, &e.color, e.target))
            .map(|(i, _)| EdgeId::from_usize(i))
            .collect();
        ids.into_iter()
            .map(|id| self.remove_edge(id).expect("the edge is live"))
            .collect()
    }

    /// The ids of the edges in the out-list of `state` for which `keep` holds, in list order.
    fn out_edge_ids(&self, state: u32, mut keep: impl FnMut(usize) -> bool) -> Vec<EdgeId> {
        let mut ids = Vec::new();
        let mut next = self
            .states
            .get(state as usize)
            .map_or(NONE, |s| s.first_out_edge());
        while next != NONE {
            if keep(next as usize) {
                ids.push(EdgeId(next));
            }
            next = self.edges[next as usize].out_next;
        }
        ids
    }

    /// The ids of the edges in the in-list of `state` for which `keep` holds, in list order.
    fn in_edge_ids(&self, state: u32, mut keep: impl FnMut(usize) -> bool) -> Vec<EdgeId> {
        let mut ids = Vec::new();
        let mut next = self
            .states
            .get(state as usize)
            .map_or(NONE, |s| s.first_in_edge());
        while next != NONE {
            if keep(next as usize) {
                ids.push(EdgeId(next));
            }
            next = self.edges[next as usize].in_next;
        }
        ids
    }

    /// Removes the edges with the given ids and returns them. Ids stay valid, so the order does
    /// not matter.
    fn remove_edge_ids(&mut self, ids: Vec<EdgeId>) -> Vec<EdgeTuple<Self>> {
        ids.into_iter()
            .filter_map(|id| self.remove_edge(id))
            .collect()
    }

    fn out_edge_position(&self, from: u32, matcher: impl Matcher<A::Expression>) -> Option<usize> {
        let mut idx = self.states.get(from as usize)?.first_out_edge();
        while idx != NONE {
            let edge = &self.edges[idx as usize];
            if matcher.matches(&edge.expression) {
                return Some(idx as usize);
            }
            idx = edge.out_next;
        }
        None
    }

    /// Gives back the memory of removed states and edges. States and edges are renumbered
    /// consecutively, keeping their order, so **all previously handed out indices and edge ids are
    /// invalidated**. The returned [`Compaction`] translates old ones into new ones.
    pub fn compact(&mut self) -> Compaction {
        let mut state_map = vec![None; self.states.len()];
        let mut next = 0;
        for (i, s) in self.states.iter().enumerate() {
            if s.is_occupied() {
                state_map[i] = Some(next);
                next += 1;
            }
        }
        let mut edge_map = vec![None; self.edges.len()];
        let mut next = 0;
        for (i, e) in self.edges.iter().enumerate() {
            if e.is_live() {
                edge_map[i] = Some(EdgeId(next));
                next += 1;
            }
        }
        let edge = |old: u32| {
            if old == NONE {
                NONE
            } else {
                edge_map[old as usize]
                    .expect("links only point to live edges")
                    .0
            }
        };
        let state = |old: u32| state_map[old as usize].expect("edges only touch occupied states");

        let mut edges = Vec::with_capacity(self.live_edges);
        for mut e in std::mem::take(&mut self.edges) {
            if !e.is_live() {
                continue;
            }
            e.source = state(e.source);
            e.target = state(e.target);
            e.out_prev = edge(e.out_prev);
            e.out_next = edge(e.out_next);
            e.in_prev = edge(e.in_prev);
            e.in_next = edge(e.in_next);
            edges.push(e);
        }
        let mut states = Vec::with_capacity(state_map.len());
        for s in std::mem::take(&mut self.states) {
            match s {
                LinkedState::Vacant => {}
                LinkedState::Occupied(c, out, inn) => {
                    states.push(LinkedState::Occupied(c, edge(out), edge(inn)))
                }
            }
        }
        self.states = states;
        self.edges = edges;
        Compaction {
            states: state_map,
            edges: edge_map,
        }
    }

    /// Turns `self` into a deterministic transition system. If `self` is not deterministic,
    /// it is returned unchanged as the error.
    pub fn try_into_deterministic(self) -> Result<Det<Self>, Self> {
        Det::try_new(self)
    }

    /// Checks the invariants of the data structure and panics if one is violated:
    /// - all links point to live edges that share the respective endpoint and are linked back,
    /// - tombstones are in no list and states that are vacant have no edges,
    /// - every live edge is in the out-list of its source and in the in-list of its target,
    /// - the number of live edges is correct.
    pub fn check_consistency(&self) {
        let live = |i: u32| {
            assert!(
                (i as usize) < self.edges.len() && self.edges[i as usize].is_live(),
                "link to edge {i} which is not live"
            )
        };
        let mut seen_out = vec![false; self.edges.len()];
        let mut seen_in = vec![false; self.edges.len()];
        for (q, state) in self.states.iter().enumerate() {
            if state.is_vacant() {
                continue;
            }
            let (mut prev, mut next) = (NONE, state.first_out_edge());
            while next != NONE {
                live(next);
                let e = &self.edges[next as usize];
                assert_eq!(e.source as usize, q, "edge {next} is in the wrong out-list");
                assert_eq!(e.out_prev, prev, "broken out-list at edge {next}");
                assert!(!seen_out[next as usize], "cycle in out-list of state {q}");
                seen_out[next as usize] = true;
                (prev, next) = (next, e.out_next);
            }
            let (mut prev, mut next) = (NONE, state.first_in_edge());
            while next != NONE {
                live(next);
                let e = &self.edges[next as usize];
                assert_eq!(e.target as usize, q, "edge {next} is in the wrong in-list");
                assert_eq!(e.in_prev, prev, "broken in-list at edge {next}");
                assert!(!seen_in[next as usize], "cycle in in-list of state {q}");
                seen_in[next as usize] = true;
                (prev, next) = (next, e.in_next);
            }
        }
        let mut count = 0;
        for (i, e) in self.edges.iter().enumerate() {
            if e.is_live() {
                count += 1;
                assert!(
                    self.contains_state(e.source),
                    "edge {i} starts in a removed state"
                );
                assert!(
                    self.contains_state(e.target),
                    "edge {i} ends in a removed state"
                );
                assert!(seen_out[i], "edge {i} is not in its out-list");
                assert!(seen_in[i], "edge {i} is not in its in-list");
            } else {
                assert!(!seen_out[i] && !seen_in[i], "removed edge {i} is linked");
            }
        }
        assert_eq!(count, self.live_edges, "wrong number of edges");
    }
}

impl<A: Alphabet, Q: Color, C: Color, X: Color + PartialEq> LinkedTs<A, (X, Q), C> {
    /// Drops the first component of the state colors, the inverse of pairing them (see
    /// [`Self::zip_state_indices`]).
    pub fn unzip_state_color(self) -> LinkedTs<A, Q, C> {
        LinkedTs {
            alphabet: self.alphabet,
            edges: self.edges,
            live_edges: self.live_edges,
            states: self
                .states
                .into_iter()
                .map(|s| s.map_occupied(|(_, q)| q))
                .collect(),
        }
    }

    /// Returns the index of the first state whose color has `left` as its first component.
    pub fn old_to_new(&self, left: X) -> Option<StateIndex<Self>> {
        self.states_with_color()
            .find_map(|(i, c)| if c.0.eq(&left) { Some(i) } else { None })
    }

    /// Returns the first component of the color of the state with the given index.
    pub fn new_to_old(&self, right: StateIndex<Self>) -> Option<X> {
        self.state_color(right).map(|c| c.0.clone())
    }
}

impl<A: Alphabet, Q: Color, C: Color> Sproutable for LinkedTs<A, Q, C> {
    type Storage = Linked;

    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        let id = u32::try_from(self.states.len())
            .ok()
            .filter(|id| *id != NONE)
            .expect("too many states for 32 bit ids");
        self.states.push(LinkedState::new(color));
        id
    }
    fn add_edge<E>(&mut self, t: E) -> EdgeId
    where
        E: IntoEdgeTuple<Self>,
    {
        let (q, a, c, p) = t.into_edge_tuple();
        self.insert_edge(q, a, c, p)
    }

    fn edge_color_mut(&mut self, id: EdgeId) -> Option<&mut EdgeColor<Self>> {
        LinkedTs::edge_color_mut(self, id)
    }

    fn state_color_mut(&mut self, state: StateIndex<Self>) -> Option<&mut StateColor<Self>> {
        LinkedTs::state_color_mut(self, state)
    }
}

impl<A: Alphabet, Q: Color, C: Color> Det<LinkedTs<A, Q, C>> {
    /// The number of edges, tombstones not counted.
    pub fn edge_count(&self) -> usize {
        self.0.edge_count()
    }

    /// One more than the largest [`EdgeId`] that was handed out so far.
    pub fn edge_bound(&self) -> usize {
        self.0.edge_bound()
    }

    /// The edge with the given id, if it exists.
    pub fn edge_by_id(&self, id: EdgeId) -> Option<EdgeOf<'_, Self>> {
        self.0.edge_by_id(id)
    }

    /// Gives back the memory of removed states and edges, see [`LinkedTs::compact`]. All previously
    /// handed out indices and edge ids are invalidated.
    pub fn compact(&mut self) -> Compaction {
        self.0.compact()
    }

    /// Checks the invariants of the data structure and that the system is deterministic, and
    /// panics if one is violated, see [`LinkedTs::check_consistency`].
    pub fn check_consistency(&self) {
        self.0.check_consistency();
        assert!(
            self.0.is_deterministic(),
            "deterministic system is not deterministic"
        );
    }

    /// Pairs the color of every state with its index, see [`LinkedTs::zip_state_indices`].
    pub fn zip_state_indices(self) -> Det<LinkedTs<A, (DefaultIdType, Q), C>> {
        Det(self.0.zip_state_indices())
    }

    /// Maps the colors of the states with `state_f`, which also gets the index of the state. Compacts
    /// first, see [`LinkedTs::linked_map_states`].
    pub fn linked_map_states<QQ: Color>(
        self,
        state_f: impl Fn(StateIndex<Self>, Q) -> QQ,
    ) -> Det<LinkedTs<A, QQ, C>> {
        Det(self.0.linked_map_states(state_f))
    }

    /// Maps the colors of the edges with `color_f`, which gets source, expression, color and target
    /// of an edge. Compacts first.
    pub fn linked_map_edge_colors<CC: Color>(
        self,
        color_f: impl Fn(
            StateIndex<Self>,
            &EdgeExpression<Self>,
            EdgeColor<Self>,
            StateIndex<Self>,
        ) -> CC,
    ) -> Det<LinkedTs<A, Q, CC>> {
        Det(self.0.linked_map_edges(|q, e, c, p| {
            let color = color_f(q, &e, c, p);
            (e, color)
        }))
    }
}

impl<A: Alphabet, Q: Color, C: Color, X: Color + PartialEq> Det<LinkedTs<A, (X, Q), C>> {
    /// Drops the first component of the state colors, see [`LinkedTs::unzip_state_color`].
    pub fn unzip_state_color(self) -> Det<LinkedTs<A, Q, C>> {
        Det(self.0.unzip_state_color())
    }
}

impl<A: Alphabet, Q: Color, C: Color> Sproutable for Det<LinkedTs<A, Q, C>> {
    type Storage = Det<Linked>;

    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        self.0.add_state(color)
    }

    /// Adds the edge and replaces all edges that overlap with it.
    fn add_edge<E>(&mut self, t: E) -> EdgeId
    where
        E: IntoEdgeTuple<Self>,
    {
        let (q, a, c, p) = t.into_edge_tuple();
        let overlapping = self
            .0
            .out_edge_ids(q, |e| a.matches(&self.0.edges[e].expression));
        for id in overlapping {
            trace!("replacing overlapping edge {id} in deterministic system");
            self.0.remove_edge(id);
        }
        self.0.insert_edge(q, a, c, p)
    }

    fn edge_color_mut(&mut self, id: EdgeId) -> Option<&mut EdgeColor<Self>> {
        self.0.edge_color_mut(id)
    }

    fn state_color_mut(&mut self, state: StateIndex<Self>) -> Option<&mut StateColor<Self>> {
        self.0.state_color_mut(state)
    }
}

impl<A: Alphabet, Q: Color, C: Color> Deterministic for Det<LinkedTs<A, Q, C>> {
    /// Scans the out-list of `state` for an edge matching `symbol`; there is no constant-time lookup yet.
    #[inline]
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        let position = self.0.out_edge_position(state, symbol)?;
        Some(
            self.0.edges[position]
                .as_edge_ref()
                .with_id(EdgeId::from_usize(position)),
        )
    }
}

impl<A: Alphabet> Storage<A> for Det<Linked> {
    type Ts<QQ: Color, CC: Color> = Det<LinkedTs<A, QQ, CC>>;

    fn try_from_linked<QQ: Color, CC: Color>(
        ts: LinkedTs<A, QQ, CC>,
    ) -> Result<Self::Ts<QQ, CC>, LinkedTs<A, QQ, CC>> {
        Det::try_new(ts)
    }
}

impl<A: Alphabet, Q: Color, C: Color> Shrinkable for LinkedTs<A, Q, C> {
    fn remove_edge(&mut self, id: EdgeId) -> Option<EdgeTuple<Self>> {
        LinkedTs::remove_edge(self, id)
    }

    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.linked_remove_state(state)
    }

    fn remove_edges_to(
        &mut self,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        if !self.contains_state(target) {
            trace!("cannot remove edges to state that does not exist");
            return None;
        }
        let ids = self.in_edge_ids(target, |_| true);
        Some(self.remove_edge_ids(ids))
    }
}

impl<Q, C> LinkedTs<CharAlphabet, Q, C> {
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
    ///
    /// Further, state 0 should be initial and colored `true` and state 1 should be colored `false`. This can be done as follows
    /// ```
    /// use automata::{Void, ts::Builder};
    ///
    /// let ts = Builder::default()
    ///     .with_state_colors([true, false]) // colors given in the order of the states
    ///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 0)])
    ///     .into_dfa(0); // 0 is the initial state
    /// ```
    pub fn builder() -> Builder<Q, C> {
        Builder::default()
    }
}

impl<Q, C> Det<LinkedTs<CharAlphabet, Q, C>> {
    /// Returns a transition system builder, see [`LinkedTs::builder`].
    pub fn builder() -> Builder<Q, C> {
        Builder::default()
    }
}

impl<A: Alphabet, Q: Color, C: Color> TransitionSystem for LinkedTs<A, Q, C> {
    type StateIndex = DefaultIdType;

    type StateColor = Q;

    type EdgeColor = C;

    type EdgesFromIter<'this>
        = LinkedEdgesFrom<'this, A::Expression, C>
    where
        Self: 'this;

    type Alphabet = A;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        let state = self.states.get(state.into_usize())?;
        if state.is_vacant() {
            return None;
        }
        Some(LinkedEdgesFrom::new(&self.edges, state.first_out_edge()))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.states
            .get(state.into_usize())?
            .color()
            .map(Cow::Borrowed)
    }

    fn state_bound(&self) -> Option<usize> {
        Some(self.states.len())
    }
}

impl<A: Alphabet, Q: Color, C: Color> States for LinkedTs<A, Q, C> {
    type StatesIter<'this>
        = LinkedStateIndices<'this, Q>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        LinkedStateIndices(&self.states, 0)
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        self.states
            .get(index.into_usize())
            .is_some_and(|s| s.is_occupied())
    }
}

/// Iterates over the indices of the states of a [`LinkedTs`], skipping removed ones.
pub struct LinkedStateIndices<'ts, Q: Color>(&'ts [LinkedState<Q>], usize);

impl<Q: Color> Iterator for LinkedStateIndices<'_, Q> {
    type Item = DefaultIdType;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.0.get(self.1) {
            self.1 += 1;
            if state.is_occupied() {
                return Some(DenseId::from_usize(self.1 - 1));
            }
        }
        None
    }
}

impl<A: Alphabet, Q: Color, C: Color> ForAlphabet<A> for LinkedTs<A, Q, C> {
    fn for_alphabet(alphabet: A) -> Self {
        Self::with_capacity(alphabet, 0)
    }

    fn for_alphabet_size_hint(from: A, size_hint: usize) -> Self {
        Self {
            alphabet: from,
            states: Vec::with_capacity(size_hint),
            edges: vec![],
            live_edges: 0,
        }
    }
}

impl<A: Alphabet, Q: Color, C: Color> PredecessorIterable for LinkedTs<A, Q, C> {
    type EdgesToIter<'this>
        = LinkedEdgesTo<'this, A::Expression, C>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        let state = self.states.get(state.into_usize())?;
        if state.is_vacant() {
            return None;
        }
        Some(LinkedEdgesTo::new(&self.edges, state.first_in_edge()))
    }
}

impl<A: Alphabet, Q, C: Clone + Hash + Eq> LinkedTs<A, Q, C> {
    /// The edges leaving `q` as a set, to compare systems regardless of the order of their edges.
    fn edge_set(&self, q: u32) -> math::FxIndexSet<(&A::Expression, Cow<'_, C>, u32)>
    where
        A::Expression: Hash + Eq,
    {
        LinkedEdgesFrom::new(&self.edges, self.states[q as usize].first_out_edge())
            .map(|e| {
                let (expression, target) = (e.expression(), e.target());
                (expression, e.into_color(), target)
            })
            .collect()
    }
}

/// Two systems are equal if they have the same alphabet and the same number of states, and every
/// state has the same color and the same set of edges in both. Note that this compares state
/// indices, so it is not an isomorphism check: systems that differ only by a renaming of the
/// states are not equal. Removed states and edges are not compared.
impl<A: Alphabet + PartialEq, Q: Hash + Debug + Eq, C: Clone + Hash + Debug + Eq> PartialEq
    for LinkedTs<A, Q, C>
{
    fn eq(&self, other: &Self) -> bool {
        if self.alphabet != other.alphabet {
            trace!("alphabets do not match");
            return false;
        }
        if self.states.len() != other.states.len() {
            trace!("number of states does not match");
            return false;
        }

        self.states
            .iter()
            .zip(other.states.iter())
            .enumerate()
            .all(|(q, (x, y))| {
                if x.is_vacant() || y.is_vacant() {
                    return x.is_vacant() && y.is_vacant();
                }
                x.color() == y.color() && self.edge_set(q as u32) == other.edge_set(q as u32)
            })
    }
}

impl<A: Alphabet + PartialEq, Q: Hash + Debug + Eq, C: Clone + Hash + Debug + Eq> Eq
    for LinkedTs<A, Q, C>
{
}

impl<A: Alphabet + std::fmt::Debug, Q: Color, C: Color> std::fmt::Debug for LinkedTs<A, Q, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for q in self.states() {
            write!(f, "{q} : {:?} |", self.state_color(q).unwrap())?;
            let Some(it) = self.edges_from(q) else {
                continue;
            };
            for e in it {
                write!(
                    f,
                    " {}/{:?}->{}",
                    e.expression().show(),
                    e.color(),
                    e.target()
                )?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::States;
    use crate::TransitionSystem;
    use crate::alphabet::CharAlphabet;
    use crate::ts::DenseId;
    use crate::ts::{Builder, Deterministic, ForAlphabet, Shrinkable, Sproutable};

    #[test]
    fn is_deterministic_compares_all_edge_pairs() {
        // the two edges on 'a' are not adjacent in this edge list
        let nts = Builder::default()
            .with_state_colors([0, 0, 0])
            .with_edges([(0, 'a', 0u32, 1), (0, 'b', 0, 1), (0, 'a', 0, 2)])
            .into_nts();
        assert!(!nts.is_deterministic());
        assert!(nts.try_into_deterministic().is_err());

        let nts = Builder::default()
            .with_state_colors([0, 0, 0])
            .with_edges([(0, 'a', 0u32, 1), (0, 'b', 0, 1), (1, 'a', 0, 2)])
            .into_nts();
        assert!(nts.is_deterministic());
        assert!(nts.try_into_deterministic().is_ok());
    }

    #[test]
    fn equality_is_symmetric() {
        let small = Builder::default()
            .with_state_colors([0, 0])
            .with_edges([(0, 'a', 0u32, 1), (1, 'a', 0, 0), (1, 'b', 0, 1)])
            .into_dts();
        let big = Builder::default()
            .with_state_colors([0, 0])
            .with_edges([
                (0, 'a', 0u32, 1),
                (1, 'a', 0, 0),
                (1, 'b', 0, 1),
                (0, 'b', 0, 0),
            ])
            .into_dts();
        assert!(small != big);
        assert!(big != small);
        assert!(small == small.clone());
    }

    #[test]
    fn dts_equality() {
        let first = Builder::default()
            .with_state_colors([0, 1])
            .with_edges([
                (0, 'a', 100u32, 0),
                (0, 'b', 1000, 1),
                (1, 'a', 200, 0),
                (1, 'b', 2000, 1),
            ])
            .into_dts();
        let second = Builder::default()
            .with_state_colors([0, 1])
            .with_edges([
                (0, 'b', 1000, 1),
                (1, 'b', 2000, 1),
                (0, 'a', 100u32, 0),
                (1, 'a', 200, 0),
            ])
            .into_dts();
        assert!(first == second, "equality should disregard order of edges");
    }

    /// Builds a nondeterministic TS with parallel edges and loops from a fixed pseudo random sequence.
    fn tangle(n: u32) -> crate::NTS<CharAlphabet, u32, u32> {
        let mut ts = crate::NTS::for_alphabet(CharAlphabet::of_size(2));
        for q in 0..n {
            ts.add_state(q);
        }
        let mut x = 12345u64;
        let mut next = |bound: u32| {
            x = x
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            ((x >> 33) % bound as u64) as u32
        };
        for c in 0..(6 * n) {
            let sym = ['a', 'b'][next(2) as usize];
            ts.add_edge((next(n), sym, c, next(n)));
        }
        ts
    }

    fn sorted(
        mut edges: Vec<crate::ts::EdgeTuple<crate::NTS<CharAlphabet, u32, u32>>>,
    ) -> Vec<(u32, char, u32, u32)> {
        edges.sort();
        edges
    }

    #[test]
    fn list_walking_removal_agrees_with_full_scan() {
        let n = 8;
        for q in 0..n {
            for p in 0..n {
                let (mut fast, mut slow) = (tangle(n), tangle(n));
                let a = fast.remove_edges_between(q, p).unwrap();
                let b = slow.filter_remove_edges(|s, _, _, t| s == q && t == p);
                assert_eq!(sorted(a), sorted(b));
                fast.check_consistency();
                assert_eq!(fast.state_count(), slow.state_count());

                let a = fast.remove_edges_between_matching(q, p, 'a');
                let b = slow.filter_remove_edges(|s, e, _, t| s == q && t == p && *e == 'a');
                assert_eq!(sorted(a.unwrap()), sorted(b));
                fast.check_consistency();
            }
            let (mut fast, mut slow) = (tangle(n), tangle(n));
            let a = fast.remove_edges_from_matching(q, 'b').unwrap();
            let b = slow.filter_remove_edges(|s, e, _, _| s == q && *e == 'b');
            assert_eq!(sorted(a), sorted(b));
            fast.check_consistency();
            let a = fast.remove_edges_from(q).unwrap();
            let b = slow.filter_remove_edges(|s, _, _, _| s == q);
            assert_eq!(sorted(a), sorted(b));
            fast.check_consistency();
            let a = fast.remove_edges_to(q).unwrap();
            let b = slow.filter_remove_edges(|_, _, _, t| t == q);
            assert_eq!(sorted(a), sorted(b));
            fast.check_consistency();

            // removing a state removes all edges around it, loops included
            let mut ts = tangle(n);
            let before = ts.edge_count();
            let touching = tangle(n)
                .filter_remove_edges(|s, _, _, t| s == q || t == q)
                .len();
            assert!(ts.remove_state(q).is_some());
            ts.check_consistency();
            assert_eq!(ts.edge_count(), before - touching);
        }
    }

    #[test]
    fn remove_edge() {
        let mut ts = crate::DTS::for_alphabet(CharAlphabet::of_size(2));

        ts.add_state(0);
        ts.add_state(1);
        ts.add_edge((0, 'a', 1));
        ts.add_edge((1, 'a', 0));
        ts.add_edge((0, 'b', 0));
        ts.add_edge((1, 'b', 1));

        assert!(ts.remove_edge(crate::ts::EdgeId(0)).is_some());
        assert!(ts.remove_edge(crate::ts::EdgeId(0)).is_none());
        assert_eq!(ts.successor(0, 'a'), None);

        ts.add_edge((0, 'a', 0));
        assert_eq!(ts.successor(0, 'a'), Some(0));
        assert_eq!(
            ts.reachable_state_indices_from(0).collect::<Vec<_>>(),
            vec![0]
        );
    }

    #[test]
    fn edge_ids_are_stable_and_not_reused() {
        use crate::ts::EdgeId;
        let mut ts = tangle(5);
        let ids: Vec<EdgeId> = (0..ts.edge_bound()).map(EdgeId::from_usize).collect();
        let kept: Vec<_> = ids.iter().filter(|id| id.0 % 3 != 0).copied().collect();
        let before: Vec<_> = kept
            .iter()
            .map(|id| ts.edge_by_id(*id).unwrap().into_tuple())
            .collect();
        for id in ids.iter().filter(|id| id.0 % 3 == 0) {
            assert!(ts.remove_edge(*id).is_some());
            ts.check_consistency();
        }
        let after: Vec<_> = kept
            .iter()
            .map(|id| ts.edge_by_id(*id).unwrap().into_tuple())
            .collect();
        assert_eq!(before, after);
        assert!(ts.edge_by_id(EdgeId(0)).is_none());

        // a new edge never takes the id of a removed one
        let fresh = ts.insert_edge(0, 'a', 99, 0);
        assert_eq!(fresh.into_usize(), ids.len());
        ts.check_consistency();
    }

    #[test]
    fn color_mut_changes_colors() {
        use crate::ts::EdgeId;
        let mut ts = tangle(3);
        *ts.state_color_mut(1).unwrap() = 77;
        assert_eq!(ts.state_color(1).unwrap().into_owned(), 77);
        *ts.edge_color_mut(EdgeId(2)).unwrap() = 55;
        assert_eq!(*ts.edge_by_id(EdgeId(2)).unwrap().color(), 55);
        assert!(ts.state_color_mut(3).is_none());
        assert!(ts.edge_color_mut(EdgeId(10_000)).is_none());
        ts.remove_edge(EdgeId(2));
        assert!(ts.edge_color_mut(EdgeId(2)).is_none());
    }

    #[test]
    fn compact_renumbers_and_keeps_structure() {
        use crate::ts::EdgeId;
        let mut ts = tangle(6);
        ts.remove_state(2);
        ts.remove_edge(EdgeId(3));
        let reference = ts.clone();
        let edges_before = ts.edge_count();
        let map = ts.compact();
        ts.check_consistency();
        assert_eq!(ts.edge_count(), edges_before);
        assert_eq!(ts.edge_bound(), edges_before);
        assert_eq!(ts.state_count(), 5);
        assert_eq!(map.state(2), None);
        assert_eq!(map.state(3), Some(2));
        assert_eq!(map.edge(EdgeId(3)), None);
        for q in reference.states() {
            let new = map.state(q).unwrap();
            assert_eq!(ts.state_color(new), reference.state_color(q));
            let mut old_edges: Vec<_> = reference
                .edges_from(q)
                .unwrap()
                .map(|e| (map.state(e.target()).unwrap(), *e.expression(), *e.color()))
                .collect();
            let mut new_edges: Vec<_> = ts
                .edges_from(new)
                .unwrap()
                .map(|e| (e.target(), *e.expression(), *e.color()))
                .collect();
            old_edges.sort();
            new_edges.sort();
            assert_eq!(old_edges, new_edges);
        }
    }

    #[test]
    fn predecessors_after_removal() {
        use crate::ts::PredecessorIterable;
        let mut ts = tangle(4);
        ts.remove_edges_from(1);
        ts.remove_state(3);
        ts.check_consistency();
        for q in ts.states().collect::<Vec<_>>() {
            let mut preds: Vec<_> = ts.predecessors(q).unwrap().map(|e| e.source()).collect();
            let mut expected: Vec<_> = ts
                .states()
                .flat_map(|p| {
                    ts.edges_from(p)
                        .unwrap()
                        .filter(move |e| e.target() == q)
                        .map(|e| e.source())
                        .collect::<Vec<_>>()
                })
                .collect();
            preds.sort();
            expected.sort();
            assert_eq!(preds, expected);
        }
        assert!(ts.predecessors(3).is_none());
    }

    #[test]
    fn det_replaces_overlapping_edges() {
        use crate::ts::{Det, Linked, Storage};
        let mut ts = crate::DTS::for_alphabet(CharAlphabet::of_size(2));
        ts.add_state(0);
        ts.add_state(1);
        let first = ts.add_edge((0, 'a', 7u32, 1));
        let second = ts.add_edge((0, 'a', 8u32, 0));
        assert_ne!(first, second);
        assert_eq!(ts.edge_count(), 1);
        assert!(ts.edge_by_id(first).is_none());
        assert_eq!(ts.edge(0, 'a').unwrap().id(), Some(second));
        assert_eq!(ts.successor(0, 'a'), Some(0));
        ts.check_consistency();

        // the storage family decides determinism
        let mut nts = crate::NTS::<CharAlphabet, u32, u32>::for_alphabet(CharAlphabet::of_size(2));
        nts.add_state(0);
        nts.add_edge((0, 'a', 1, 0));
        nts.add_edge((0, 'a', 2, 0));
        assert_eq!(nts.edge_count(), 2);
        assert!(<Linked as Storage<CharAlphabet>>::try_from_linked(nts.clone()).is_ok());
        assert!(<Det<Linked> as Storage<CharAlphabet>>::try_from_linked(nts).is_err());
    }

    #[test]
    fn det_shrinks_like_linked() {
        use crate::ts::EdgeId;
        let mut ts = tangle(6).try_into_deterministic().unwrap_or_else(|nts| {
            // the tangle is nondeterministic, keep the first edge per state and symbol
            let mut det =
                crate::DTS::<CharAlphabet, u32, u32>::for_alphabet(CharAlphabet::of_size(2));
            for q in nts.states() {
                det.add_state(*nts.state_color(q).unwrap());
            }
            for q in nts.states() {
                for e in nts.edges_from(q).unwrap() {
                    det.add_edge((e.source(), *e.expression(), *e.color(), e.target()));
                }
            }
            det
        });
        ts.check_consistency();
        let total = ts.edge_count();
        let removed = ts.remove_edges_to(2).unwrap();
        ts.check_consistency();
        assert_eq!(ts.edge_count(), total - removed.len());
        let removed = ts.remove_edges_from_matching(0, 'a');
        ts.check_consistency();
        assert!(removed.unwrap().len() <= 1);
        assert!(ts.remove_state(1).is_some());
        ts.check_consistency();
        assert!(ts.remove_edge(EdgeId(1_000_000)).is_none());
    }
}
