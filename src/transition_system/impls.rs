#![allow(unused)]
#![allow(missing_docs)]
use crate::prelude::*;

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

#[cfg(feature = "petgraph")]
pub(crate) mod pg;

use super::ScalarIdType;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id<Typ = DefaultIdType>(pub Typ);
impl<Idx: IdType> Show for Id<Idx> {
    fn show(&self) -> String {
        self.0.show()
    }
}
impl<Typ> std::borrow::Borrow<Typ> for Id<Typ> {
    fn borrow(&self) -> &Typ {
        &self.0
    }
}
impl<Typ: IdType> Display for Id<Typ> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Id({})", self.0.show())
    }
}

pub fn q<IdType: ScalarIdType>(n: usize) -> IdType {
    IdType::from_usize(n)
}

pub trait TransitionSystemImplementation {
    type Indeterminate<A: Alphabet, Q: Color, C: Color, const DET: bool>: TransitionSystem<
        Alphabet = A,
        StateColor = Q,
        EdgeColor = C,
    >;

    fn new_deterministic<A: Alphabet, Q: Color, C: Color>(
        alphabet: A,
    ) -> Self::Indeterminate<A, Q, C, true>
    where
        Self::Indeterminate<A, Q, C, true>: Deterministic;
    fn new_for_alphabet<A: Alphabet, Q: Color, C: Color, const DET: bool>(
        alphabet: A,
    ) -> Self::Indeterminate<A, Q, C, DET>;

    fn is_deterministic<A: Alphabet, Q: Color, C: Color, const DET: bool>(
        ts: &Self::Indeterminate<A, Q, C, DET>,
    ) -> bool {
        if DET {
            if !ts.is_deterministic() {
                panic!("This transition system is not deterministic even though the type indicates it!");
            }
            true
        } else {
            ts.is_deterministic()
        }
    }
}

pub struct EdgeListsBased;
pub struct LinkedListBased;

pub struct PetgraphBased;

impl TransitionSystemImplementation for EdgeListsBased {
    type Indeterminate<A: Alphabet, Q: Color, C: Color, const DET: bool> = EdgeLists<A, Q, C, DET>;

    fn new_deterministic<A: Alphabet, Q: Color, C: Color>(
        alphabet: A,
    ) -> Self::Indeterminate<A, Q, C, true>
    where
        Self::Indeterminate<A, Q, C, true>: Deterministic,
    {
        EdgeLists::for_alphabet(alphabet)
    }

    fn new_for_alphabet<A: Alphabet, Q: Color, C: Color, const DET: bool>(
        alphabet: A,
    ) -> Self::Indeterminate<A, Q, C, DET> {
        EdgeLists::for_alphabet(alphabet)
    }
}
impl TransitionSystemImplementation for LinkedListBased {
    type Indeterminate<A: Alphabet, Q: Color, C: Color, const DET: bool> =
        LinkedListTransitionSystem<A, Q, C, DET>;

    fn new_deterministic<A: Alphabet, Q: Color, C: Color>(
        alphabet: A,
    ) -> Self::Indeterminate<A, Q, C, true>
    where
        Self::Indeterminate<A, Q, C, true>: Deterministic,
    {
        LinkedListTransitionSystem::for_alphabet(alphabet)
    }

    fn new_for_alphabet<A: Alphabet, Q: Color, C: Color, const DET: bool>(
        alphabet: A,
    ) -> Self::Indeterminate<A, Q, C, DET> {
        LinkedListTransitionSystem::for_alphabet(alphabet)
    }
}
