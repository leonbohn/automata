use std::fmt::Debug;

use crate::prelude::*;
use petgraph::{
    data::Build,
    graph::{EdgeIndex, EdgeReference, EdgeReferences, Node, NodeIndex},
    prelude as pg,
    visit::{EdgeRef, IntoEdgesDirected, IntoNeighborsDirected},
    Directed,
    Direction::{Incoming, Outgoing},
};

use super::{DefaultId, Id};

pub type Graph<Q, E> = pg::DiGraph<Q, E, DefaultId>;

pub type EdgeLabel<T> = (EdgeExpression<T>, EdgeColor<T>);

impl From<petgraph::graph::NodeIndex> for Id {
    fn from(idx: NodeIndex) -> Self {
        idx.index().into()
    }
}
impl Id {
    pub fn into_node_index(self) -> NodeIndex {
        NodeIndex::new(self.0 as usize)
    }
}
pub struct GraphTs<
    A: Alphabet = CharAlphabet,
    Q: Color = Void,
    C: Color = Void,
    const DET: bool = true,
> {
    alphabet: A,
    graph: Graph<Q, (A::Expression, C)>,
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> Shrinkable for GraphTs<A, Q, C, DET> {
    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        let q = state.into();
    }

    fn remove_edges_from_matching(
        &mut self,
        source: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }

    fn remove_edges_between_matching(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }

    fn remove_edges_between(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }

    fn remove_edges_from(
        &mut self,
        source: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }

    fn remove_edges_to(
        &mut self,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::transition_system::EdgeTuple<Self>>> {
        todo!()
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> GraphTs<A, Q, C, DET> {
    pub fn into_deterministic(self) -> GraphTs<A, Q, C, true> {
        match self.try_into_deterministic() {
            Ok(ts) => ts,
            Err(ts) => {
                tracing::error!("Tried to convert non-deterministic transition system to deterministic one\n{:?}", ts);
                panic!("This transition system is not deterministic");
            }
        }
    }

    pub fn try_into_deterministic(self) -> Result<GraphTs<A, Q, C, true>, Self> {
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
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> Debug for GraphTs<A, Q, C, DET> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> TransitionSystem for GraphTs<A, Q, C, DET> {
    type Alphabet = A;

    type StateIndex = Id;

    type StateColor = Q;

    type EdgeColor = C;

    type EdgeRef<'this> = GraphTsEdgeRef<'this, A,  C>
    where
        Self: 'this;

    type EdgesFromIter<'this> = std::iter::Map<petgraph::graph::Edges<'this, (A::Expression, C), Directed>, fn(EdgeReference<'this, (A::Expression, C)>) -> Self::EdgeRef<'this>>
    where
        Self: 'this;

    type StateIndices<'this> = std::iter::Map<petgraph::graph::NodeIndices<>, fn(NodeIndex) -> Id>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        todo!()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        if !self.contains_state_index(state) {
            return None;
        }
        let q = state.into_node_index();
        Some(
            self.graph
                .edges_directed(q, Outgoing)
                .map(GraphTsEdgeRef::from),
        )
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        if !self.contains_state_index(state) {
            return None;
        }
        let q = state.into_node_index();
        Some(self.graph[q].clone())
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> ForAlphabet<A> for GraphTs<A, Q, C, DET> {
    fn for_alphabet(from: A) -> Self {
        Self {
            alphabet: from,
            graph: Graph::new(),
        }
    }
    fn for_alphabet_size_hint(from: A, _size_hint: (usize, usize)) -> Self {
        Self {
            alphabet: from,
            graph: Graph::with_capacity(_size_hint.0, _size_hint.1),
        }
    }
}

impl Show for NodeIndex {
    fn show(&self) -> String {
        self.index().to_string()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GraphTsEdgeRef<'a, A: Alphabet, C: Color> {
    pub source: NodeIndex,
    pub target: NodeIndex,
    pub expression: &'a A::Expression,
    pub color: C,
    pub index: EdgeIndex,
}

impl<'a, A: Alphabet, C: Color> From<EdgeReference<'a, (A::Expression, C)>>
    for GraphTsEdgeRef<'a, A, C>
{
    fn from(value: EdgeReference<'a, (A::Expression, C)>) -> Self {
        Self {
            source: value.source(),
            target: value.target(),
            expression: &value.weight().0,
            color: value.weight().1.clone(),
            index: value.id(),
        }
    }
}

impl<'a, A: Alphabet, C: Color> IsEdge<'a, <A as alphabet::Alphabet>::Expression, Id, C>
    for GraphTsEdgeRef<'a, A, C>
{
    fn target(&self) -> Id {
        self.target.into()
    }

    fn color(&self) -> C {
        self.color.clone()
    }

    fn expression(&self) -> &'a <A as alphabet::Alphabet>::Expression {
        &self.expression
    }

    fn source(&self) -> Id {
        Id(self.source.index() as u32)
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> PredecessorIterable
    for GraphTs<A, Q, C, DET>
{
    type PreEdgeRef<'this> = GraphTsEdgeRef<'this, A,  C>
    where
        Self: 'this;

    type EdgesToIter<'this> = std::iter::Map<petgraph::graph::Edges<'this, (A::Expression, C), Directed>, fn(EdgeReference<'this, (A::Expression, C)>) -> Self::PreEdgeRef<'this>>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        let q = state.into_node_index();
        if !self.graph.contains_node(q) {
            return None;
        }
        Some(
            self.graph
                .edges_directed(q, Incoming)
                .map(GraphTsEdgeRef::from),
        )
    }
}

impl<A: Alphabet, Q: Color, C: Color> Deterministic for GraphTs<A, Q, C, true> {}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> Sproutable for GraphTs<A, Q, C, DET> {
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        self.graph.add_node(color)
    }

    fn add_edge<E>(&mut self, t: E) -> Option<Self::EdgeRef<'_>>
    where
        E: IntoEdgeTuple<Self>,
    {
        let (q, e, c, p) = t.into_edge_tuple();
        let idx = Graph::add_edge(&mut self.graph, q, p, (e, c));
        let (e, c) = &self.graph[idx];
        Some(GraphTsEdgeRef {
            source: q,
            target: p,
            expression: &e,
            color: c.clone(),
            index: idx,
        })
    }

    fn set_state_color(&mut self, index: StateIndex<Self>, color: StateColor<Self>) {
        let q = index.into_node_index();
        assert!(self.graph.contains_node(q));
        self.graph[q] = color;
    }
}

fn recast<A: Alphabet, Q: Color, C: Color, const DET: bool, const OUT_DET: bool>(
    ts: GraphTs<A, Q, C, DET>,
) -> GraphTs<A, Q, C, OUT_DET> {
    if !DET && OUT_DET && !ts.is_deterministic() {
        panic!("cannot convert non-deterministic transition system to deterministic");
    }
    let GraphTs { alphabet, graph } = ts;
    GraphTs { alphabet, graph }
}
