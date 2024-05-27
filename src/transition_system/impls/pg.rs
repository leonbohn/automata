use crate::prelude::*;
use crate::transition_system::EdgeReference;
pub use petgraph;
pub use petgraph::prelude::*;
pub use petgraph::stable_graph as sg;

#[derive(Debug, Clone)]
pub struct GraphTs<
    A: Alphabet = CharAlphabet,
    Q: Color = Void,
    C: Color = Void,
    const DET: bool = true,
> {
    alphabet: A,
    graph: StableDiGraph<Q, (A::Expression, C), DefaultIdType>,
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> GraphTs<A, Q, C, DET> {
    pub(crate) fn try_recast<const ND: bool>(self) -> Result<GraphTs<A, Q, C, ND>, Self> {
        if DET {
            assert!(self.is_deterministic());
        }
        Ok(GraphTs {
            alphabet: self.alphabet,
            graph: self.graph,
        })
    }
    pub(crate) fn try_into_deterministic(self) -> Result<GraphTs<A, Q, C, true>, Self> {
        if DET {
            assert!(self.is_deterministic());
        } else if !self.is_deterministic() {
            return Err(self);
        }
        Ok(GraphTs {
            alphabet: self.alphabet,
            graph: self.graph,
        })
    }
}

impl<Q: Color, C: Color, const DET: bool> GraphTs<CharAlphabet, Q, C, DET> {
    pub fn builder() -> TSBuilder<Q, C, DET> {
        TSBuilder::default()
    }
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

        if DET
            && (self.edges_matching(source, &expression)?.next().is_some()
                || !self.contains_state_index(target))
        {
            return None;
        }

        let edge = self
            .graph
            .add_edge(node_index(source), node_index(target), (expression, color));
        let (e, c) = self.graph.edge_weight(edge)?;
        Some(EdgeReference::new(source, e, c, target))
    }
    fn set_state_color(&mut self, index: StateIndex<Self>, color: StateColor<Self>) {
        self.graph[node_index(index)] = color;
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> Shrinkable for GraphTs<A, Q, C, DET> {
    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        let color = self.graph.remove_node(node_index(state))?;
        Some(color)
    }
    fn remove_edges_from_matching(
        &mut self,
        source: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
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
        source: StateIndex<Self>,
        target: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
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
        source: StateIndex<Self>,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
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
        source: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let mut removed = Vec::new();
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
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        let mut removed = Vec::new();
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

    type EdgesFromIter<'this> = std::iter::Map<sg::Edges<'this, (A::Expression, C), Directed, StateIndex<Self>>, fn(sg::EdgeReference<'this, (A::Expression, C), StateIndex<Self>>) -> Self::EdgeRef<'this>>
    where
        Self: 'this;

    type StateIndices<'this> = std::iter::Map<sg::NodeIndices<'this, Q, StateIndex<Self>>, fn(sg::NodeIndex) -> StateIndex<Self>>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.graph.node_indices().map(state_index)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(
            self.graph
                .edges_directed(node_index(state), Direction::Outgoing)
                .map(|edge| {
                    let (expression, color) = edge.weight();
                    EdgeReference::new(
                        state_index(edge.source()),
                        expression,
                        color,
                        state_index(edge.target()),
                    )
                }),
        )
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.graph.node_weight(node_index(state)).cloned()
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

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        let walker = self
            .graph
            .neighbors_directed(node_index(state), Direction::Incoming)
            .detach();
        Some(PgEdgesIter {
            graph: &self.graph,
            walker,
            target: state,
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

#[cfg(test)]
mod tests {
    use super::GraphTs;
    use crate::prelude::*;

    #[test]
    fn petgraph_impl() {
        let mut pgts: GraphTs<CharAlphabet, bool, Void> =
            GraphTs::for_alphabet(CharAlphabet::of_size(3));
        let q0 = pgts.add_state(true);
        let q1 = pgts.add_state(false);
        let q2 = pgts.add_state(false);
        let q3 = pgts.add_state(false);

        pgts.add_edge((q0, 'a', q0));
        pgts.add_edge((q0, 'b', q1));
        pgts.add_edge((q0, 'c', q3));
        pgts.add_edge((q1, 'a', q1));
        pgts.add_edge((q1, 'b', q2));
        pgts.add_edge((q2, 'a', q2));
        pgts.add_edge((q2, 'b', q0));

        // test iteration direction
        let succs: math::Set<_> = pgts.reachable_state_indices_from(q0).collect();
        assert_eq!(succs, math::Set::from_iter([q0, q1, q3, q2]));

        let mut dfa = pgts.into_dfa_with_initial(0);

        for pos in ["", "bbb", "abababa", "a"] {
            assert!(dfa.accepts(pos))
        }
        for neg in ["ab", "aba", "bbbab"] {
            assert!(!dfa.accepts(neg))
        }

        assert_eq!(dfa.remove_edges_between(q2, q0).unwrap().len(), 1);
        assert_eq!(dfa.reached_state_index("abbab"), None);
        assert_eq!(dfa.reached_state_index("abaab"), Some(q2));

        dfa.remove_state(q2);
        assert_eq!(dfa.reached_state_index("abab"), None);
    }
}
