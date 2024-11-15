pub use indices::*;
use petgraph::visit::{IntoEdgeReferences, IntoEdgesDirected};
mod indices {
    use super::*;
    use std::marker::PhantomData;

    // #[cfg(not(feature = "large_index"))]
    pub type DefaultIndexType = u32;
    // #[cfg(feature = "large_index")]
    // pub type DefaultIndexType = u64;

    #[derive(Debug, Clone, Eq, PartialEq, Copy)]
    pub struct Id<Pos, Ty> {
        n: Ty,
        _phantom: PhantomData<Pos>,
    }
    impl<Pos, Ty> std::ops::Deref for Id<Pos, Ty> {
        type Target = Ty;
        fn deref(&self) -> &Self::Target {
            &self.n
        }
    }
    impl<Pos, Ty> std::ops::DerefMut for Id<Pos, Ty> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.n
        }
    }

    pub struct NodeIndex;
    pub type VId<Ty = u32> = Id<NodeIndex, Ty>;
    pub struct EdgeIndex;
    pub type EId<Ty = u32> = Id<EdgeIndex, Ty>;

    pub trait Access {
        type Out<G: Game>;
        fn access<G: Game>(self, game: &G) -> Option<&Self::Out<G>>;
    }

    impl From<petgraph::graph::NodeIndex> for VId {
        fn from(value: petgraph::graph::NodeIndex) -> Self {
            todo!()
        }
    }
    impl From<VId> for petgraph::graph::NodeIndex {
        fn from(value: VId) -> Self {
            todo!()
        }
    }
    impl Access for VId {
        type Out<G: Game> = G::V;

        fn access<G: Game>(self, game: &G) -> Option<&Self::Out<G>> {
            game.access_node(&self)
        }
    }

    impl Access for EId {
        type Out<G: Game> = G::E;

        fn access<G: Game>(self, game: &G) -> Option<&Self::Out<G>> {
            game.access_edge(&self)
        }
    }
    impl From<petgraph::graph::EdgeIndex> for VId {
        fn from(value: petgraph::graph::EdgeIndex) -> Self {
            todo!()
        }
    }
    impl From<EId> for petgraph::graph::EdgeIndex {
        fn from(value: EId) -> Self {
            todo!()
        }
    }
}

pub trait Game {
    type V;
    type E;

    fn access_node(&self, node_index: VId) -> Option<&Self::V>;
    fn access_edge(&self, edge_index: EId) -> Option<&Self::E>;

    fn state_indices(&self) -> impl Iterator<Item = VId>;
    fn outgoing_edge_indices(&self, source: VId) -> impl Iterator<Item = EId>;
    fn incoming_edge_indices(&self, target: VId) -> impl Iterator<Item = EId>;
}

pub trait IntoGame<V, E> {
    type IntoG: Game<V = V, E = E>;
    fn into_game(self) -> Self::IntoG;
}

impl<V, E> Game for crate::PetGame<V, E, DefaultIndexType> {
    type V = V;

    type E = E;

    fn access_node(&self, node_index: VId) -> Option<&Self::V> {
        self.node_weight(node_index.into())
    }

    fn access_edge(&self, edge_index: EId) -> Option<&Self::E> {
        self.edge_weight(edge_index.into())
    }

    fn state_indices(&self) -> impl Iterator<Item = VId> {
        self.node_indices().map(|idx| idx.into())
    }

    fn outgoing_edge_indices(&self, source: VId) -> impl Iterator<Item = EId> {
        self.edges_directed(source.into(), petgraph::Outgoing)
    }

    fn incoming_edge_indices(&self, target: VId) -> impl Iterator<Item = EId> {
        todo!()
    }
}
