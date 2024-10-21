use crate::prelude::*;

/// A weak priority mapping is a right congruence with edge colors.
#[derive(Clone, Debug)]
pub struct WeakPriorityMapping<A: Alphabet = CharAlphabet, C: Color = Int>(
    RightCongruence<A, Void, C>,
);

impl<A: Alphabet, C: Color> WeakPriorityMapping<A, C> {
    pub fn into_moore(self) -> MooreMachine<A, C, Void> {
        todo!()
    }
}

impl<A: Alphabet, C: Color> Deterministic for WeakPriorityMapping<A, C> {}

impl<A: Alphabet, C: Color> PredecessorIterable for WeakPriorityMapping<A, C> {
    type PreEdgeRef<'this> = <RightCongruence<A, C, C> as PredecessorIterable>::PreEdgeRef<'this>
    where
        Self: 'this;

    type EdgesToIter<'this> = <RightCongruence<A, C, C> as PredecessorIterable>::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        self.0.predecessors(state)
    }
}

impl<A: Alphabet, C: Color> TransitionSystem for WeakPriorityMapping<A, C> {
    type Alphabet = A;

    type StateIndex = DefaultIdType;

    type StateColor = Void;

    type EdgeColor = C;

    type EdgeRef<'this> = <RightCongruence<A, Void, C> as TransitionSystem>::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this> = <RightCongruence<A, Void, C> as TransitionSystem>::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this> = <RightCongruence<A, Void, C> as TransitionSystem>::StateIndices<'this>
    where
        Self: 'this;

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        self.0.edges_from(state)
    }

    fn alphabet(&self) -> &Self::Alphabet {
        self.0.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.0.state_indices()
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.0.state_color(state)
    }
}
