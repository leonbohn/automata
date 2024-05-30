#![allow(unused)]
#![allow(missing_docs)]
use crate::prelude::*;

pub(crate) mod pg;

pub(crate) mod edge_lists;
use std::{
    fmt::{Debug, Display},
    ops::Deref,
};

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
impl Show for DefaultIdType {
    fn show(&self) -> String {
        self.to_string()
    }
}
// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
// pub struct Id<Typ = DefaultIdType>(pub Typ);
// impl<Typ> std::borrow::Borrow<Typ> for Id<Typ> {
//     fn borrow(&self) -> &Typ {
//         &self.0
//     }
// }
// impl<Typ: IndexType> Display for Id<Typ> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "Id({:?})", self.0)
//     }
// }

// pub trait IntoId<Typ: IndexType = DefaultIdType> {
//     fn into_id(self) -> Id<Typ>;
// }
