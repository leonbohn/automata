use crate::{math::Map, math::Set, prelude::*, transition_system::EdgeReference};
use std::{fmt::Debug, hash::Hash};

use self::alphabet::Matches;

/// An implementation of a transition system with states of type `Q` and colors of type `C`. It stores
/// the states and edges in a vector, which allows for fast access and iteration. The states and edges
/// are indexed by their position in the respective vector.
#[derive(Clone, PartialEq, Eq)]
pub struct MutableTs<
    A: Alphabet,
    Q = crate::Void,
    C: Hash + Eq = crate::Void,
    Idx: IndexType = usize,
> {
    pub(crate) alphabet: A,
    pub(crate) states: Map<Idx, MutableTsState<A, Q, C, Idx>>,
}

/// Type alias that takes a [`TransitionSystem`] and gives the type of a corresponding [`MutableTs`], i.e. one
/// with the same alphabet, edge and state colors.
pub type IntoMutableTs<Ts> = MutableTs<
    <Ts as TransitionSystem>::Alphabet,
    <Ts as TransitionSystem>::StateColor,
    <Ts as TransitionSystem>::EdgeColor,
>;

impl<A: Alphabet, Idx: IndexType, C: Clone + Hash + Eq, Q: Clone> MutableTs<A, Q, C, Idx> {
    /// Creates a new transition system with the given alphabet.
    pub fn new(alphabet: A) -> Self {
        Self {
            alphabet,
            states: Map::default(),
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
    pub(crate) fn from_parts(alphabet: A, states: Map<Idx, MutableTsState<A, Q, C, Idx>>) -> Self {
        Self { alphabet, states }
    }

    /// Decomposes the `MutableTs` into its constituent parts.
    #[allow(clippy::type_complexity)]
    pub(crate) fn into_parts(self) -> (A, Map<Idx, MutableTsState<A, Q, C, Idx>>) {
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
            states: (0..states)
                .map(|i| {
                    (
                        i.into(),
                        MutableTsState::new(<StateColor<Self> as Default>::default()),
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
    pub fn raw_state_map(&self) -> &Map<Idx, MutableTsState<A, Q, C, Idx>> {
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

impl<A: Alphabet, Q: Clone + Hash + Eq, C: Clone + Hash + Eq, Index: IndexType>
    crate::transition_system::Shrinkable for MutableTs<A, Q, C, Index>
{
    fn remove_state<Idx: Indexes<Self>>(&mut self, state: Idx) -> Option<Q> {
        self.mutablets_remove_state(state.to_index(self)?)
    }
    fn remove_all_matching(
        &mut self,
        source: impl Indexes<Self>,
        matcher: impl Matches<EdgeExpression<Self>>,
    ) -> Option<
        Set<(
            EdgeExpression<Self>,
            EdgeColor<Self>,
            crate::transition_system::StateIndex<Self>,
        )>,
    > {
        let q = source.to_index(self)?;
        self.states
            .get_mut(&q)
            .map(|s| s.remove_all_matching(matcher))
    }
    fn remove_first_matching(
        &mut self,
        source: impl Indexes<Self>,
        matcher: impl Matches<EdgeExpression<Self>>,
    ) -> Option<(
        EdgeExpression<Self>,
        EdgeColor<Self>,
        crate::transition_system::StateIndex<Self>,
    )> {
        let q = source.to_index(self)?;
        self.states
            .get_mut(&q)
            .and_then(|s| s.remove_edge_matching(matcher))
    }
}

impl<A: Alphabet, Idx: IndexType, Q: Clone, C: Clone + Hash + Eq> MutableTs<A, Q, C, Idx> {
    /// Returns an iterator over the [`EdgeIndex`]es of the edges leaving the given state.
    pub(crate) fn mutablets_edges_from(
        &self,
        source: Idx,
    ) -> Option<impl Iterator<Item = (&'_ A::Expression, &'_ (Idx, C))> + '_> {
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
pub struct MutableTsState<A: Alphabet, Q, C: Hash + Eq, Idx: IndexType> {
    color: Q,
    edges: Map<A::Expression, (Idx, C)>,
    predecessors: Set<(Idx, A::Expression, C)>,
}

impl<A: Alphabet, Q, C: Hash + Eq, Idx: IndexType> MutableTsState<A, Q, C, Idx> {
    /// Creates a new state with the given color.
    pub fn new(color: Q) -> Self {
        Self {
            color,
            edges: Map::default(),
            predecessors: Set::default(),
        }
    }

    pub fn set_color(&mut self, color: Q) {
        self.color = color;
    }

    pub fn predecessors(&self) -> &Set<(Idx, A::Expression, C)> {
        &self.predecessors
    }

    pub fn add_pre_edge(&mut self, from: Idx, on: A::Expression, color: C) -> bool {
        self.predecessors.insert((from, on, color))
    }

    pub fn remove_pre_edge(&mut self, from: Idx, on: A::Expression, color: C) -> bool {
        self.predecessors.remove(&(from, on, color))
    }

    pub fn remove_incoming_edges_from(&mut self, target: Idx) {
        self.predecessors.retain(|(idx, _, _)| *idx != target);
    }

    pub fn remove_outgoing_edges_to(&mut self, target: Idx) {
        self.edges.retain(|_, (idx, _)| *idx != target);
    }

    pub fn edges(&self) -> impl Iterator<Item = (&A::Expression, &(Idx, C))> {
        self.edges.iter()
    }

    pub fn edge_map(&self) -> &Map<A::Expression, (Idx, C)> {
        &self.edges
    }

    pub fn add_edge(&mut self, on: A::Expression, color: C, to: Idx) -> Option<(Idx, C)> {
        self.edges.insert(on, (to, color))
    }

    pub fn remove_edge_matching(
        &mut self,
        m: impl Matches<A::Expression>,
    ) -> Option<(A::Expression, C, Idx)> {
        let (on, _) = self.edges.iter().find(|(e, _)| m.matches(e))?;
        let expr = on.clone();
        self.edges
            .remove(&expr)
            .map(|(to, color)| (expr, color, to))
    }

    pub fn remove_all_matching(
        &mut self,
        m: impl Matches<A::Expression>,
    ) -> Set<(A::Expression, C, Idx)> {
        let expressions: Vec<_> = self
            .edges
            .iter()
            .filter_map(|(e, _)| if m.matches(e) { Some(e.clone()) } else { None })
            .collect();
        expressions
            .into_iter()
            .map(move |e| {
                let (to, color) = self.edges.remove(&e).unwrap();
                (e, color, to)
            })
            .collect()
    }

    pub fn remove_edge(&mut self, on: &A::Expression) -> Option<(Idx, C)> {
        self.edges.remove(on)
    }

    pub fn recolor<P: Color>(self, color: P) -> MutableTsState<A, P, C, Idx> {
        MutableTsState {
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

impl<A: Alphabet, IdxTy: IndexType, Q: Clone, C: Clone + Hash + Eq> TransitionSystem
    for MutableTs<A, Q, C, IdxTy>
{
    type StateColor = Q;
    type EdgeColor = C;
    type StateIndex = IdxTy;
    type EdgeRef<'this> = EdgeReference<'this, A::Expression, IdxTy, C> where Self: 'this;
    type EdgesFromIter<'this> = MutableTsEdgesFrom<'this, A::Expression, IdxTy, C> where Self: 'this;
    type StateIndices<'this> = std::iter::Cloned<std::collections::hash_map::Keys<'this, IdxTy, MutableTsState<A, Q, C, IdxTy>>> where Self: 'this;

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
        let source = state.to_index(self)?;
        Some(MutableTsEdgesFrom::new(
            source,
            self.raw_state_map()
                .get(&source)
                .map(|o| o.edge_map().iter())?,
        ))
    }
}

/// Specialized iterator over the edges that leave a given state in a [`MutableTs`].
pub struct MutableTsEdgesFrom<'ts, E, Idx, C> {
    edges: std::collections::hash_map::Iter<'ts, E, (Idx, C)>,
    source: Idx,
}

impl<'ts, E, Idx, C> MutableTsEdgesFrom<'ts, E, Idx, C> {
    /// Creates a new instance from the given components.
    pub fn new(source: Idx, edges: std::collections::hash_map::Iter<'ts, E, (Idx, C)>) -> Self {
        Self { edges, source }
    }
}

impl<'ts, E, Idx: IndexType, C> Iterator for MutableTsEdgesFrom<'ts, E, Idx, C> {
    type Item = EdgeReference<'ts, E, Idx, C>;

    fn next(&mut self) -> Option<Self::Item> {
        self.edges
            .next()
            .map(|(e, (t, c))| EdgeReference::new(self.source, e, c, *t))
    }
}

impl<A, C, Q, Idx> std::fmt::Debug for MutableTs<A, Q, C, Idx>
where
    A: Alphabet,
    C: Debug + Clone + Hash + Eq,
    Q: Debug + Clone + Hash + Eq,
    Idx: IndexType,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{}",
            self.build_transition_table(
                |idx, c| format!("{} : {:?}", idx.show(), c),
                |edge| format!("{:?}->{}", edge.color(), edge.target().show())
            )
        )
    }
}

impl<A: Alphabet, Q: Clone, C: Clone + Hash + Eq> Sproutable for MutableTs<A, Q, C, usize> {
    /// Adds a state with given `color` to the transition system, returning the index of
    /// the new state.
    fn add_state<X: Into<StateColor<Self>>>(&mut self, color: X) -> Self::StateIndex {
        let id = self.states.len();
        let state = MutableTsState::new(color.into());
        self.states.insert(id, state);
        id
    }

    fn add_edge<E>(&mut self, t: E) -> Option<(Self::StateIndex, Self::EdgeColor)>
    where
        E: IntoEdgeTuple<Self>,
    {
        let (q, a, c, p) = t.into_edge_tuple();

        assert!(
            self.contains_state(q) && self.contains_state(p),
            "Source {} or target {} vertex does not exist in the graph.",
            q,
            p
        );
        self.states
            .get_mut(&q)
            .expect("We know this exists")
            .add_pre_edge(q, a.clone(), c.clone());
        self.states.get_mut(&q).and_then(|o| o.add_edge(a, c, p))
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

    fn remove_edges<X: Indexes<Self>>(
        &mut self,
        from: X,
        on: <Self::Alphabet as Alphabet>::Expression,
    ) -> bool {
        let Some(from) = from.to_index(self) else {
            return false;
        };
        let target = self.states.get_mut(&from).and_then(|o| o.remove_edge(&on));
        if let Some((target, color)) = target {
            let removed = self
                .states
                .get_mut(&target)
                .expect("Something must have gone wrong...")
                .remove_pre_edge(from, on, color);
            debug_assert!(removed);
            true
        } else {
            false
        }
    }
}

impl<A: Alphabet, Q: Clone + Hash + Eq, C: Clone + Hash + Eq> ForAlphabet for MutableTs<A, Q, C> {
    fn for_alphabet(from: A) -> Self {
        Self {
            alphabet: from,
            states: Map::default(),
        }
    }
}
