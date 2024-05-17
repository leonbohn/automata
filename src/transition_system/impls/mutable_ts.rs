use super::Idx;
use crate::{math::Map, math::Set, prelude::*, transition_system::EdgeReference};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Debug, Display},
    hash::Hash,
    ops::Deref,
};

use self::alphabet::Matcher;

/// An implementation of a transition system with states of type `Q` and colors of type `C`. It stores
/// the states and edges in a vector, which allows for fast access and iteration. The states and edges
/// are indexed by their position in the respective vector.
#[derive(Clone, PartialEq, Eq)]
pub struct MutableTs<A: Alphabet, Q = crate::Void, C: Hash + Eq = crate::Void> {
    pub(crate) alphabet: A,
    pub(crate) states: BTreeMap<Idx, MutableTsState<A, Q, C>>,
}

/// Type alias that takes a [`TransitionSystem`] and gives the type of a corresponding [`MutableTs`], i.e. one
/// with the same alphabet, edge and state colors.
pub type IntoMutableTs<Ts> = MutableTs<
    <Ts as TransitionSystem>::Alphabet,
    <Ts as TransitionSystem>::StateColor,
    <Ts as TransitionSystem>::EdgeColor,
>;

impl<A: Alphabet, C: Clone + Hash + Eq, Q: Clone> MutableTs<A, Q, C> {
    /// Creates a new transition system with the given alphabet.
    pub fn new(alphabet: A) -> Self {
        Self {
            alphabet,
            states: BTreeMap::default(),
        }
    }

    pub(crate) fn mutablets_remove_state(&mut self, idx: Idx) -> Option<Q> {
        let state = self.states.remove(&idx)?;
        self.states.iter_mut().for_each(|(_, s)| {
            s.remove_incoming_edges_from(idx);
            s.remove_outgoing_edges_to(idx)
        });
        Some(state.color)
    }

    /// Creates a `MutableTs` from the given alphabet and states.
    pub(crate) fn from_parts(alphabet: A, states: BTreeMap<Idx, MutableTsState<A, Q, C>>) -> Self {
        Self { alphabet, states }
    }

    /// Decomposes the `MutableTs` into its constituent parts.
    #[allow(clippy::type_complexity)]
    pub(crate) fn into_parts(self) -> (A, BTreeMap<Idx, MutableTsState<A, Q, C>>) {
        (self.alphabet, self.states)
    }

    /// Creates an empty `MutableTs` ensuring the given capacity.
    pub fn with_capacity(alphabet: A, states: usize) -> Self
    where
        StateColor<Self>: Default,
        Idx: From<usize> + IndexType,
    {
        Self {
            alphabet,
            states:
                (0..states)
                    .map(|i| {
                        (
                            i.into(),
                            MutableTsState::new_with_intial_id(
                                <StateColor<Self> as Default>::default(),
                            ),
                        )
                    })
                    .collect(),
        }
    }

    /// Gets a mutable reference to the alphabet of the transition system.
    pub fn alphabet(&self) -> &A {
        &self.alphabet
    }

    /// Returns a reference to the underlying statemap.
    pub fn raw_state_map(&self) -> &BTreeMap<Idx, MutableTsState<A, Q, C>> {
        &self.states
    }

    /// Attempts to find the index of a state with the given `color`. If no such state is
    /// found, `None` is returned. Note, that the function simply returns the first state
    /// with the given color. As the order in which the states are stored is not guaranteed,
    /// subsequent calls may lead to different results, if two states with the same color
    /// exist.
    #[inline(always)]
    pub fn find_by_color(&self, color: &Q) -> Option<Idx>
    where
        Q: Eq,
    {
        self.states.iter().find_map(|(idx, state)| {
            if state.color() == color {
                Some(*idx)
            } else {
                None
            }
        })
    }

    /// Returns an iterator emitting pairs of state indices and their colors.
    pub fn indices_with_color(&self) -> impl Iterator<Item = (Idx, &StateColor<Self>)> {
        self.states.iter().map(|(idx, state)| (*idx, state.color()))
    }
}

impl<A: Alphabet, Q: Clone + Hash + Eq, C: Clone + Hash + Eq> crate::transition_system::Shrinkable
    for MutableTs<A, Q, C>
{
    fn remove_state<Idx: Indexes<Self>>(&mut self, state: Idx) -> Option<Q> {
        self.mutablets_remove_state(state.to_index(self)?)
    }
    fn remove_edges_from_matching(
        &mut self,
        source: impl Indexes<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }
    fn remove_edge<'a>(
        &'a mut self,
        edge: crate::transition_system::EdgeRef<'a, Self>,
    ) -> Option<crate::transition_system::EdgeTuple<Self>> {
        todo!()
    }

    fn remove_edges_between_matching(
        &mut self,
        source: impl Indexes<Self>,
        target: impl Indexes<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let q = source.to_index(self)?;
        let p = target.to_index(self)?;

        let mut removed = vec![];

        Some(removed)
    }

    fn remove_edges_between(
        &mut self,
        source: impl Indexes<Self>,
        target: impl Indexes<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }

    fn remove_edges_from(
        &mut self,
        source: impl Indexes<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }
}

impl<A: Alphabet, Q: Clone, C: Clone + Hash + Eq> MutableTs<A, Q, C> {
    /// Returns an iterator over the [`EdgeIndex`]es of the edges leaving the given state.
    pub(crate) fn mutablets_edges_from(
        &self,
        source: Idx,
    ) -> Option<impl Iterator<Item = &'_ (A::Expression, C, Idx)> + '_> {
        self.states.get(&source).map(|s| s.edges.iter())
    }

    /// Checks whether the state exists.
    pub fn contains_state<I: Into<Idx>>(&self, index: I) -> bool {
        self.states.contains_key(&index.into())
    }
}

/// A state in a transition system. This stores the color of the state and the index of the
/// first edge leaving the state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct MutableTsState<A: Alphabet, Q, C: Hash + Eq> {
    id: Idx,
    color: Q,
    edges: Vec<(A::Expression, C, Idx)>,
    predecessors: Vec<(Idx, A::Expression, C)>,
}

impl<A: Alphabet, Q, C: Hash + Eq> MutableTsState<A, Q, C> {
    pub fn new_with_intial_id(color: Q) -> Self {
        Self {
            id: Idx::initial(),
            color,
            edges: Default::default(),
            predecessors: Default::default(),
        }
    }

    /// Creates a new state with the given color.
    pub fn new(id: Idx, color: Q) -> Self {
        Self {
            id,
            color,
            edges: Default::default(),
            predecessors: Default::default(),
        }
    }

    pub fn set_color(&mut self, color: Q) {
        self.color = color;
    }

    pub fn predecessors(&self) -> &[(Idx, A::Expression, C)] {
        &self.predecessors
    }

    pub fn add_pre_edge(&mut self, from: Idx, on: A::Expression, color: C) {
        debug_assert!(
            !self
                .predecessors
                .iter()
                .any(|(idx, e, c)| *idx == from && e == &on && c == &color),
            "Predecessor edge already exists!"
        );

        self.predecessors.push((from, on, color))
    }

    pub(crate) fn remove_pre_edge(
        &mut self,
        from: Idx,
        on: &A::Expression,
        color: &C,
    ) -> Option<(Idx, A::Expression, C)> {
        if let Some(position) = self
            .predecessors
            .iter()
            .position(|(idx, e, c)| *idx == from && e == on && c == color)
        {
            Some(self.predecessors.swap_remove(position))
        } else {
            None
        }
    }

    pub(crate) fn remove_out_edge(
        &mut self,
        on: &A::Expression,
        color: &C,
        to: Idx,
    ) -> Option<(A::Expression, C, Idx)> {
        if let Some(position) = self
            .edges
            .iter()
            .position(|(e, c, q)| *q == to && e == on && c == color)
        {
            Some(self.edges.swap_remove(position))
        } else {
            None
        }
    }

    pub fn remove_incoming_edges_from(&mut self, target: Idx) {
        self.predecessors.retain(|(idx, _, _)| *idx != target);
    }

    pub fn remove_outgoing_edges_to(&mut self, target: Idx) {
        self.edges.retain(|(_e, _c, q)| *q != target);
    }

    pub fn edges(&self) -> std::slice::Iter<'_, (A::Expression, C, Idx)> {
        self.edges.iter()
    }

    pub fn edge_map(&self) -> &[(A::Expression, C, Idx)] {
        &self.edges
    }

    pub fn add_edge(&mut self, on: A::Expression, color: C, to: Idx) {
        debug_assert!(
            !self
                .edges
                .iter()
                .any(|(e, c, q)| e == &on && c == &color && *q == to),
            "Edge already exists."
        );

        self.edges.push((on, color, to));
    }

    pub fn recolor<P: Color>(self, color: P) -> MutableTsState<A, P, C> {
        MutableTsState {
            id: self.id,
            color,
            edges: self.edges,
            predecessors: self.predecessors,
        }
    }

    /// Obtains a reference to the color of the state.
    pub fn color(&self) -> &Q {
        &self.color
    }
}

impl<A: Alphabet, Q: Clone, C: Clone + Hash + Eq> TransitionSystem for MutableTs<A, Q, C> {
    type StateColor = Q;
    type EdgeColor = C;
    type StateIndex = Idx;
    type EdgeRef<'this> = EdgeReference<'this, A::Expression, Idx, C> where Self: 'this;
    type StateIndices<'this> = std::iter::Cloned<std::collections::btree_map::Keys<'this, Idx, MutableTsState<A, Q, C>>> where Self: 'this;

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
        Some(EdgesFrom::new(q, self.states.get(&q).unwrap().edges.iter()))
    }
    type EdgesFromIter<'this> = EdgesFrom<'this, A::Expression, Idx, C> where Self: 'this;
}

/// Specialized iterator over the edges that leave a given state in a [`MutableTs`].
pub struct EdgesFrom<'ts, E, Idx, C> {
    edges: std::slice::Iter<'ts, (E, C, Idx)>,
    source: Idx,
}

impl<'ts, E, Idx, C> EdgesFrom<'ts, E, Idx, C> {
    /// Creates a new instance from the given components.
    pub fn new(source: Idx, edges: std::slice::Iter<'ts, (E, C, Idx)>) -> Self {
        Self { edges, source }
    }
}

impl<'ts, E, Idx: IndexType, C> Iterator for EdgesFrom<'ts, E, Idx, C> {
    type Item = EdgeReference<'ts, E, Idx, C>;

    fn next(&mut self) -> Option<Self::Item> {
        self.edges
            .next()
            .map(|(e, c, q)| EdgeReference::new(self.source, e, c, *q))
    }
}

impl<A, C, Q> std::fmt::Debug for MutableTs<A, Q, C>
where
    A: Alphabet,
    C: Debug + Clone + Hash + Eq,
    Q: Debug + Clone + Hash + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // writeln!(
        //     f,
        //     "{}",
        //     self.build_transition_table(
        //         |idx, c| format!("{} : {:?}", idx.show(), c),
        //         |edge| format!("{:?}->{}", edge.color(), edge.target().show())
        //     )
        // )
        unimplemented!("Debug for MutableTs, shold be collection of edges")
    }
}

impl<A: Alphabet, Q: Clone, C: Clone + Hash + Eq> Sproutable for MutableTs<A, Q, C> {
    /// Adds a state with given `color` to the transition system, returning the index of
    /// the new state.
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        let id = self.states.len().into();
        let state = MutableTsState::new(id, color);
        self.states.insert(id, state);
        id
    }

    fn add_edge<E>(&mut self, t: E)
    where
        E: IntoEdgeTuple<Self>,
    {
        let (q, a, c, p) = t.into_edge_tuple();

        assert!(
            self.contains_state(q) && self.contains_state(p),
            "Source {} or target {} vertex does not exist in the graph.",
            q.show(),
            p.show()
        );
        self.states
            .get_mut(&q)
            .expect("We know this exists")
            .add_pre_edge(q, a.clone(), c.clone());
        self.states.get_mut(&q).map(|o| o.add_edge(a, c, p));
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

impl<A: Alphabet, Q: Clone + Hash + Eq, C: Clone + Hash + Eq> ForAlphabet for MutableTs<A, Q, C> {
    fn for_alphabet(from: A) -> Self {
        Self {
            alphabet: from,
            states: BTreeMap::default(),
        }
    }
}
