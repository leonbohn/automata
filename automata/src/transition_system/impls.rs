#![allow(unused)]
#![allow(missing_docs)]
use crate::prelude::*;

#[cfg(feature = "petgraph")]
pub(crate) mod petgraph_backed;
#[cfg(feature = "petgraph")]
pub use petgraph_backed::{petgraph, GraphTs, GraphTsNeighborsIter};

#[cfg(feature = "implementations")]
pub(crate) mod edge_lists;
#[cfg(feature = "implementations")]
pub use edge_lists::{
    EdgeLists, EdgeListsDeterministic, EdgeListsNondeterministic, IntoEdgeLists, MutableTsState,
};

pub(crate) mod linked;
pub use linked::{
    CollectLinkedList, IntoLinkedListNondeterministic, LinkedListDeterministic,
    LinkedListNondeterministic, LinkedListTransitionSystem, LinkedListTransitionSystemEdge,
    LinkedListTransitionSystemEdgesToIter, LinkedListTransitionSystemState, NTSEdgesFromIter,
};

use super::ScalarIndexType;

pub type DefaultIdType = u32;
