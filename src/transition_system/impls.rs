#![allow(unused)]
#![allow(missing_docs)]
use crate::prelude::*;

pub(crate) mod pg;
pub use pg::{petgraph, GraphTs, GraphTsNeighborsIter};

#[cfg(feature = "implementations")]
pub(crate) mod edge_lists;
#[cfg(feature = "implementations")]
pub use edge_lists::{
    EdgeLists, EdgeListsDeterministic, EdgeListsNondeterministic, IntoEdgeLists, MutableTsState,
};
#[cfg(feature = "implementations")]
pub(crate) mod linked;
#[cfg(feature = "implementations")]
pub use linked::{
    CollectLinkedList, IntoLinkedListNondeterministic, LinkedListDeterministic,
    LinkedListNondeterministic, LinkedListTransitionSystem, LinkedListTransitionSystemEdge,
    LinkedListTransitionSystemEdgesToIter, LinkedListTransitionSystemState, NTSEdgesFromIter,
};

use super::ScalarIndexType;

pub type DefaultIdType = u32;
