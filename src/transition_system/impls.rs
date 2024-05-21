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

pub struct EdgeListsImpl;
pub struct LinkedListImpl;

impl TransitionSystemImplementation for EdgeListsImpl {
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

impl TransitionSystemImplementation for LinkedListImpl {
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
