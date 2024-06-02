use std::fmt::Debug;
use std::ops::Deref;

use crate::prelude::*;
use crate::transition_system::EdgeReference;
pub use petgraph;
pub use petgraph::prelude::*;
pub use petgraph::stable_graph as sg;
use tracing::trace;

#[derive(Debug, Clone)]
pub struct GraphTs<
    A: Alphabet = CharAlphabet,
    Q: Color = Void,
    C: Color = Void,
    const DET: bool = true,
    N: GraphTsId = DefaultIdType,
> {
    alphabet: A,
    graph: StableDiGraph<Q, (A::Expression, C), N>,
}

pub trait GraphTsId: RepresentableId + sg::IndexType + IdType {}
impl<T: RepresentableId + sg::IndexType + IdType> GraphTsId for T {}

pub(super) fn pg_to_id<N: GraphTsId>(idx: sg::NodeIndex<N>) -> Id<N> {
    Id::from(idx.index())
}
pub(super) fn id_to_pg<N: GraphTsId>(idx: Id<N>) -> sg::NodeIndex<N> {
    sg::NodeIndex::new(idx.into_usize())
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, N: GraphTsId> GraphTs<A, Q, C, DET, N> {
    pub(crate) fn try_recast<const ND: bool>(self) -> Result<GraphTs<A, Q, C, ND, N>, Self> {
        if DET {
            assert!(self.is_deterministic());
        }
        Ok(GraphTs {
            alphabet: self.alphabet,
            graph: self.graph,
        })
    }
    pub(crate) fn try_into_deterministic(self) -> Result<GraphTs<A, Q, C, true, N>, Self> {
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

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, N: GraphTsId> Sproutable
    for GraphTs<A, Q, C, DET, N>
{
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        pg_to_id(self.graph.add_node(color))
    }

    fn add_edge<E>(&mut self, t: E) -> Option<crate::transition_system::EdgeTuple<Self>>
    where
        E: IntoEdgeTuple<Self>,
    {
        let (source, expression, color, target) = t.into_edge_tuple();

        if !self.contains_state_index(source) || !self.contains_state_index(target) {
            panic!("Source or target state does not exist");
        }

        let mut out = None;
        if DET {
            if let Some(removed) = self.remove_edges_from_matching(source, &expression) {
                assert!(
                    removed.len() <= 1,
                    "Cannot have more than one overlapping edge!"
                );
                out = removed.into_iter().next();
            }
        }

        let edge = self
            .graph
            .add_edge(id_to_pg(source), id_to_pg(target), (expression, color));
        out
    }
    fn set_state_color(&mut self, index: StateIndex<Self>, color: StateColor<Self>) {
        self.graph[id_to_pg(index)] = color;
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, N: GraphTsId> Shrinkable
    for GraphTs<A, Q, C, DET, N>
{
    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        let color = self.graph.remove_node(id_to_pg(state))?;
        Some(color)
    }
    fn remove_edges_from_matching(
        &mut self,
        source: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        if !self.contains_state_index(source) {
            return None;
        }
        let mut removed = Vec::new();
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, _)| s == id_to_pg(source))
                .unwrap_or(false)
            {
                if matcher.matches(&g[e].0) {
                    removed.push((
                        pg_to_id(g.edge_endpoints(e).unwrap().0),
                        g[e].0.clone(),
                        g[e].1.clone(),
                        pg_to_id(g.edge_endpoints(e).unwrap().1),
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
        if !self.contains_state_index(source) {
            return None;
        }
        if !self.contains_state_index(target) {
            return None;
        }
        let mut removed = Vec::new();
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, t)| s == id_to_pg(source) && t == id_to_pg(target))
                .unwrap_or(false)
            {
                if matcher.matches(&g[e].0) {
                    removed.push((
                        pg_to_id(g.edge_endpoints(e).unwrap().0),
                        g[e].0.clone(),
                        g[e].1.clone(),
                        pg_to_id(g.edge_endpoints(e).unwrap().1),
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
        if !self.contains_state_index(source) {
            return None;
        }
        if !self.contains_state_index(target) {
            return None;
        }
        let mut removed = Vec::new();
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, t)| s == id_to_pg(source) && t == id_to_pg(target))
                .unwrap_or(false)
            {
                removed.push((
                    pg_to_id(g.edge_endpoints(e).unwrap().0),
                    g[e].0.clone(),
                    g[e].1.clone(),
                    pg_to_id(g.edge_endpoints(e).unwrap().1),
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
        if !self.contains_state_index(source) {
            return None;
        }
        let mut removed = Vec::new();
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, t)| s == id_to_pg(source))
                .unwrap_or(false)
            {
                removed.push((
                    pg_to_id(g.edge_endpoints(e).unwrap().0),
                    g[e].0.clone(),
                    g[e].1.clone(),
                    pg_to_id(g.edge_endpoints(e).unwrap().1),
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
        if !self.contains_state_index(target) {
            return None;
        }
        let mut removed = Vec::new();
        self.graph.retain_edges(|g, e| {
            if g.edge_endpoints(e)
                .map(|(s, t)| t == id_to_pg(target))
                .unwrap_or(false)
            {
                removed.push((
                    pg_to_id(g.edge_endpoints(e).unwrap().0),
                    g[e].0.clone(),
                    g[e].1.clone(),
                    pg_to_id(g.edge_endpoints(e).unwrap().1),
                ));
                false
            } else {
                true
            }
        });
        Some(removed)
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, N: GraphTsId> TransitionSystem
    for GraphTs<A, Q, C, DET, N>
{
    type Alphabet = A;

    type StateIndex = Id<N>;

    type StateColor = Q;

    type EdgeColor = C;

    type EdgeRef<'this> = EdgeReference<'this, A::Expression, StateIndex<Self>, EdgeColor<Self>>
    where
        Self: 'this;

    type EdgesFromIter<'this> = std::iter::Map<sg::Edges<'this, (A::Expression, C), Directed, N>, fn(sg::EdgeReference<'this, (A::Expression, C), N>) -> Self::EdgeRef<'this>>
    where
        Self: 'this;

    type StateIndices<'this> = std::iter::Map<sg::NodeIndices<'this, Q, N>, fn(sg::NodeIndex<N>) -> StateIndex<Self>>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.graph.node_indices().map(pg_to_id)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        if !self.contains_state_index(state) {
            return None;
        }
        Some(
            self.graph
                .edges_directed(id_to_pg(state), Direction::Outgoing)
                .map(|edge| {
                    let (expression, color) = edge.weight();
                    EdgeReference::new(
                        pg_to_id(edge.source()),
                        expression,
                        color,
                        pg_to_id(edge.target()),
                    )
                }),
        )
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        if !self.contains_state_index(state) {
            return None;
        }
        self.graph.node_weight(id_to_pg(state)).cloned()
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool, N: GraphTsId> PredecessorIterable
    for GraphTs<A, Q, C, DET, N>
{
    type PreEdgeRef<'this> = EdgeReference<'this, A::Expression, StateIndex<Self>, EdgeColor<Self>>
    where
        Self: 'this;

    type EdgesToIter<'this> = GraphTsNeighborsIter<'this, A, Q, C, DET, N>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        if !self.contains_state_index(state) {
            return None;
        }
        let walker = self
            .graph
            .neighbors_directed(id_to_pg(state), Direction::Incoming)
            .detach();
        Some(GraphTsNeighborsIter {
            graph: &self.graph,
            walker,
            target: *state,
        })
    }
}

pub struct GraphTsNeighborsIter<'a, A: Alphabet, Q: Color, C: Color, const DET: bool, N: GraphTsId>
{
    graph: &'a StableDiGraph<Q, (A::Expression, C), N>,
    walker: sg::WalkNeighbors<N>,
    target: N,
}

impl<'a, A: Alphabet, Q: Color, C: Color, const DET: bool, N: GraphTsId> Iterator
    for GraphTsNeighborsIter<'a, A, Q, C, DET, N>
{
    type Item = EdgeReference<
        'a,
        A::Expression,
        StateIndex<GraphTs<A, Q, C, DET, N>>,
        EdgeColor<GraphTs<A, Q, C, DET, N>>,
    >;
    fn next(&mut self) -> Option<Self::Item> {
        let (edge_id, source_id) = self.walker.next(self.graph)?;
        let (expression, color) = self.graph.edge_weight(edge_id)?;
        let source = pg_to_id(source_id);
        Some(EdgeReference::new(
            source,
            expression,
            color,
            Id(self.target),
        ))
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

impl<A: Alphabet + PartialEq, Q: Color, C: Color, const DET: bool> PartialEq
    for GraphTs<A, Q, C, DET>
{
    fn eq(&self, other: &Self) -> bool {
        if self.alphabet() != other.alphabet() {
            return false;
        }

        for l in self.state_indices() {
            let Some(r_edges) = other.edges_from(l).map(|it| it.collect::<math::Set<_>>()) else {
                return false;
            };
            let Some(l_edges) = self.edges_from(l).map(|it| it.collect::<math::Set<_>>()) else {
                return false;
            };
            if !l_edges.eq(&r_edges) {
                return false;
            }
        }
        true
    }
}
impl<A: Alphabet + PartialEq, Q: Color, C: Color, const DET: bool> Eq for GraphTs<A, Q, C, DET> {}

#[cfg(test)]
mod tests {
    use super::GraphTs;
    use crate::prelude::*;

    #[test]
    fn petgraph_overlapping() {
        let mut ts: GraphTs<CharAlphabet, Void, Void> =
            GraphTs::for_alphabet(CharAlphabet::of_size(2));
        let q0 = ts.add_state(Void);
        assert_eq!(ts.add_edge((q0, 'a', q0)), None);
        assert_eq!(ts.add_edge((q0, 'b', q0)), None);
        assert_eq!(ts.add_edge((q0, 'a', q0)), Some((q0, 'a', Void, q0)));

        let mut ts: GraphTs<CharAlphabet, Void, Void, false> =
            GraphTs::for_alphabet(CharAlphabet::of_size(2));
        let q0 = ts.add_state(Void);
        assert_eq!(ts.add_edge((q0, 'a', q0)), None);
        assert_eq!(ts.add_edge((q0, 'b', q0)), None);
        assert_eq!(ts.add_edge((q0, 'a', q0)), None);
    }

    #[test]
    fn petgraph_equality() {
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

        let other = pgts.clone();
        assert_eq!(pgts, other);
        pgts.remove_edges_between_matching(q2, q0, 'b');
        assert_ne!(pgts, other);
    }

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

        let mut dfa = pgts.into_dfa_with_initial(Id(0));

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
