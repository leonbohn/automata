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
mod petgraph;
#[cfg(feature = "petgraph")]
pub use petgraph::*;

/// Abstracts the creation of new transition systems.This trait is used to create new instances of
/// transition systems, which can be either deterministic or nondeterministic.
pub trait CreateNew {
    type Indeterminate<A: Alphabet, Q: Color, C: Color, const DET: bool>: Sized
        + TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = C>;

    /// Creates a new deterministic instance of `Self` for the given [`Alphabet`].
    fn new_deterministic<A, Q, C>(alphabet: A) -> Self::Indeterminate<A, Q, C, true>
    where
        Self::Indeterminate<A, Q, C, true>: Deterministic,
        A: Alphabet,
        Q: Color,
        C: Color;

    /// Creates an empty instance of `Self` for the given [`Alphabet`].
    fn new_for_alphabet<A, Q, C, const DET: bool>(alphabet: A) -> Self::Indeterminate<A, Q, C, DET>
    where
        A: Alphabet,
        Q: Color,
        C: Color;

    /// Creates an instance of `Self` for the given [`Alphabet`] and a hint for the size of the transition
    /// system allowing for preallocation of memory. The resulting TS should be empty.
    fn new_for_alphabet_size_hint<A, Q, C, const DET: bool>(
        alphabet: A,
        _size_hint: usize,
    ) -> Self::Indeterminate<A, Q, C, DET>
    where
        A: Alphabet,
        Q: Color,
        C: Color,
    {
        Self::new_for_alphabet(alphabet)
    }

    /// Returns whether the given transition system is deterministic, that is it contains no edges
    /// with the same source and target, but two different [`Expression`]s, that (overlap)[`Expression::overlaps`].
    ///
    /// Verifies that the const generic `DET` is correct. If `DET` is `true`, the function will panic
    /// if the transition system is not deterministic.
    fn is_deterministic<A, Q, C, const DET: bool>(ts: &Self::Indeterminate<A, Q, C, DET>) -> bool
    where
        A: Alphabet,
        Q: Color,
        C: Color,
    {
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

impl CreateNew for EdgeListsImpl {
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

pub struct LinkedListImpl;

impl CreateNew for LinkedListImpl {
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
