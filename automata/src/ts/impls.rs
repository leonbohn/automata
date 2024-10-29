#![allow(unused)]
#![allow(missing_docs)]

// #[cfg(not(feature = "petgraph"))]
// pub(crate) mod petgraph_backed;
// #[cfg(not(feature = "petgraph"))]
// pub use petgraph_backed::{petgraph, GraphTs, GraphTsNeighborsIter};

// #[cfg(not(feature = "implementations"))]
// pub(crate) mod edge_lists;
// #[cfg(not(feature = "implementations"))]
// pub use edge_lists::{
//     EdgeLists, EdgeListsDeterministic, EdgeListsNondeterministic, IntoEdgeLists, MutableTsState,
// };

pub mod packed;

pub(crate) mod linked;
pub use linked::{
    CollectLinkedList, IntoLinkedListNondeterministic, LinkedListDeterministic,
    LinkedListNondeterministic, LinkedListTransitionSystem, LinkedListTransitionSystemEdge,
    LinkedListTransitionSystemEdgesToIter, LinkedListTransitionSystemState, NTSEdgesFromIter,
};

use super::ScalarIndexType;

pub type DefaultIdType = u32;
