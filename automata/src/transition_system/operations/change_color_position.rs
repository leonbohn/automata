#[allow(unused)]
mod from_edges_to_states {
    use crate::prelude::*;

    #[derive(Debug, Clone)]
    pub struct IntoStateColored<T: TransitionSystem> {
        ts: T,
    }
}

#[allow(unused)]
mod from_states_to_edges {
    use crate::{prelude::*, transition_system::EdgeRef};

    #[derive(Debug, Clone)]
    pub struct IntoEdgeColored<T: TransitionSystem> {
        ts: T,
    }

    impl<T: PredecessorIterable> PredecessorIterable for IntoEdgeColored<T> {
        type PreEdgeRef<'this> = T::PreEdgeRef<'this>
        where
            Self: 'this;

        type EdgesToIter<'this> = T::EdgesToIter<'this>
        where
            Self: 'this;

        fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
            self.ts.predecessors(state)
        }
    }

    impl<T: Pointed> Pointed for IntoEdgeColored<T> {
        fn initial(&self) -> Self::StateIndex {
            self.ts.initial()
        }
    }

    impl<T: Deterministic> Deterministic for IntoEdgeColored<T> {}

    impl<T: TransitionSystem> TransitionSystem for IntoEdgeColored<T> {
        type Alphabet = T::Alphabet;
        type StateIndex = StateIndex<T>;
        type StateColor = StateColor<T>;
        type EdgeColor = EdgeColor<T>;
        type EdgeRef<'this> = EdgeRef<'this, T>
        where
            Self: 'this;
        type EdgesFromIter<'this> = T::EdgesFromIter<'this>
        where
            Self: 'this;
        type StateIndices<'this> = T::StateIndices<'this>
        where
            Self: 'this;
        fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
            self.ts.edges_from(state)
        }
        fn alphabet(&self) -> &Self::Alphabet {
            self.ts.alphabet()
        }
        fn state_indices(&self) -> Self::StateIndices<'_> {
            self.ts.state_indices()
        }
        fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
            self.ts.state_color(state)
        }
    }
}
