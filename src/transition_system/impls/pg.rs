use crate::prelude::*;
use crate::transition_system::EdgeReference;
pub use petgraph::prelude::*;
pub use petgraph::stable_graph as sg;

pub struct GraphTs<A: Alphabet, Q: Color, C: Color, const DET: bool> {
    alphabet: A,
    graph: StableDiGraph<Q, (A::Expression, C), DefaultIdType>,
}

pub fn node_index(id: DefaultIdType) -> sg::NodeIndex {
    sg::node_index(
        id.try_into()
            .expect("Cannot convert default id type to node index"),
    )
}
pub fn state_index(idx: sg::NodeIndex) -> DefaultIdType {
    idx.index()
        .try_into()
        .expect("Cannot convert node index to default id type")
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> Sproutable for GraphTs<A, Q, C, DET> {
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        state_index(self.graph.add_node(color))
    }

    fn add_edge<E>(&mut self, t: E) -> Option<Self::EdgeRef<'_>>
    where
        E: IntoEdgeTuple<Self>,
    {
        let (source, expression, color, target) = t.into_edge_tuple();
        let edge = self
            .graph
            .add_edge(node_index(source), node_index(target), (expression, color));
        let (e, c) = self.graph.edge_weight(edge)?;
        Some(EdgeReference::new(source, e, c, target))
    }

    fn set_state_color<Idx: Indexes<Self>, X: Into<StateColor<Self>>>(
        &mut self,
        index: Idx,
        color: X,
    ) {
        let q = index.to_index(self).unwrap();
        self.graph[node_index(q)] = color.into();
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> Shrinkable for GraphTs<A, Q, C, DET> {
    fn remove_state<Idx: Indexes<Self>>(&mut self, state: Idx) -> Option<Self::StateColor> {
        let q = state.to_index(self)?;
        let color = self.graph.remove_node(node_index(q))?;
        Some(color)
    }

    fn remove_edges_from_matching(
        &mut self,
        source: impl Indexes<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let source = source.to_index(self)?;
        let mut removed = Vec::new();
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, _)| s == node_index(source))
                .unwrap_or(false)
            {
                if matcher.matches(&g[e].0) {
                    removed.push((
                        state_index(g.edge_endpoints(e).unwrap().0),
                        g[e].0.clone(),
                        g[e].1.clone(),
                        state_index(g.edge_endpoints(e).unwrap().1),
                    ));
                    false
                } else {
                    true
                }
            } else {
                true
            }
        });
        Some(removed)
    }

    fn remove_edges_between_matching(
        &mut self,
        source: impl Indexes<Self>,
        target: impl Indexes<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let source = source.to_index(self)?;
        let target = target.to_index(self)?;
        let mut removed = Vec::new();
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, t)| s == node_index(source) && t == node_index(target))
                .unwrap_or(false)
            {
                if matcher.matches(&g[e].0) {
                    removed.push((
                        state_index(g.edge_endpoints(e).unwrap().0),
                        g[e].0.clone(),
                        g[e].1.clone(),
                        state_index(g.edge_endpoints(e).unwrap().1),
                    ));
                    false
                } else {
                    true
                }
            } else {
                true
            }
        });
        Some(removed)
    }

    fn remove_edges_between(
        &mut self,
        source: impl Indexes<Self>,
        target: impl Indexes<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let source = source.to_index(self)?;
        let target = target.to_index(self)?;
        let mut removed = Vec::new();
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, t)| s == node_index(source) && t == node_index(target))
                .unwrap_or(false)
            {
                removed.push((
                    state_index(g.edge_endpoints(e).unwrap().0),
                    g[e].0.clone(),
                    g[e].1.clone(),
                    state_index(g.edge_endpoints(e).unwrap().1),
                ));
                false
            } else {
                true
            }
        });
        Some(removed)
    }

    fn remove_edges_from(
        &mut self,
        source: impl Indexes<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let mut removed = Vec::new();
        let source = source.to_index(self)?;
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, t)| s == node_index(source))
                .unwrap_or(false)
            {
                removed.push((
                    state_index(g.edge_endpoints(e).unwrap().0),
                    g[e].0.clone(),
                    g[e].1.clone(),
                    state_index(g.edge_endpoints(e).unwrap().1),
                ));
                false
            } else {
                true
            }
        });
        Some(removed)
    }

    fn remove_edges_to(
        &mut self,
        target: impl Indexes<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let mut removed = Vec::new();
        let target = target.to_index(self)?;
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, t)| t == node_index(target))
                .unwrap_or(false)
            {
                removed.push((
                    state_index(g.edge_endpoints(e).unwrap().0),
                    g[e].0.clone(),
                    g[e].1.clone(),
                    state_index(g.edge_endpoints(e).unwrap().1),
                ));
                false
            } else {
                true
            }
        });
        Some(removed)
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> TransitionSystem for GraphTs<A, Q, C, DET> {
    type Alphabet = A;

    type StateIndex = DefaultIdType;

    type StateColor = Q;

    type EdgeColor = C;

    type EdgeRef<'this> = EdgeReference<'this, A::Expression, StateIndex<Self>, EdgeColor<Self>>
    where
        Self: 'this;

    type EdgesFromIter<'this> = PgEdgesIter<'this, A, Q, C, DET>
    where
        Self: 'this;

    type StateIndices<'this> = std::iter::Map<sg::NodeIndices<'this, Q, StateIndex<Self>>, fn(sg::NodeIndex) -> StateIndex<Self>>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.graph.node_indices().map(|idx| state_index(idx))
    }

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        let q = state.to_index(self)?;
        let walker = self
            .graph
            .neighbors_directed(node_index(q), Direction::Outgoing)
            .detach();
        Some(PgEdgesIter {
            graph: &self.graph,
            walker,
            target: q,
        })
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        let q = state.to_index(self)?;
        self.graph.node_weight(node_index(q)).cloned()
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> PredecessorIterable
    for GraphTs<A, Q, C, DET>
{
    type PreEdgeRef<'this> = EdgeReference<'this, A::Expression, StateIndex<Self>, EdgeColor<Self>>
    where
        Self: 'this;

    type EdgesToIter<'this> = PgEdgesIter<'this, A, Q, C, DET>
    where
        Self: 'this;

    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        let q = state.to_index(self)?;
        let walker = self
            .graph
            .neighbors_directed(node_index(q), Direction::Incoming)
            .detach();
        Some(PgEdgesIter {
            graph: &self.graph,
            walker,
            target: q,
        })
    }
}

pub struct PgEdgesIter<'a, A: Alphabet, Q: Color, C: Color, const DET: bool> {
    graph: &'a StableDiGraph<Q, (A::Expression, C), DefaultIdType>,
    walker: sg::WalkNeighbors<DefaultIdType>,
    target: DefaultIdType,
}

impl<'a, A: Alphabet, Q: Color, C: Color, const DET: bool> Iterator
    for PgEdgesIter<'a, A, Q, C, DET>
{
    type Item = EdgeReference<
        'a,
        A::Expression,
        StateIndex<GraphTs<A, Q, C, DET>>,
        EdgeColor<GraphTs<A, Q, C, DET>>,
    >;
    fn next(&mut self) -> Option<Self::Item> {
        let (edge_id, source_id) = self.walker.next(self.graph)?;
        let (expression, color) = self.graph.edge_weight(edge_id)?;
        let source = state_index(source_id);
        Some(EdgeReference::new(source, expression, color, self.target))
    }
}

impl<A: Alphabet, Q: Color, C: Color> Deterministic for GraphTs<A, Q, C, true> {}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> ForAlphabet<A> for GraphTs<A, Q, C, DET> {
    fn for_alphabet(from: A) -> Self {
        Self {
            alphabet: from,
            graph: StableDiGraph::default(),
        }
    }
    fn for_alphabet_size_hint(from: A, size_hint: usize) -> Self {
        Self {
            alphabet: from,
            graph: StableDiGraph::with_capacity(size_hint, 0),
        }
    }
}
