use crate::TransitionSystem;
use crate::ts::States;
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{IsEdge, StateIndex};
use std::borrow::Cow;

/// Reverses the direction of all transitions in a given [`TransitionSystem`].
#[derive(Clone, Debug)]
pub struct Reversed<Ts>(pub Ts);

impl<'ts, E, Idx, C: Clone, T: IsEdge<'ts, E, Idx, C>> IsEdge<'ts, E, Idx, C> for Reversed<T> {
    fn source(&self) -> Idx {
        self.0.target()
    }

    fn target(&self) -> Idx {
        self.0.source()
    }

    fn color(&self) -> Cow<'_, C> {
        self.0.color()
    }

    fn expression(&self) -> &'ts E {
        self.0.expression()
    }
}

impl<Ts> TransitionSystem for Reversed<Ts>
where
    Ts: PredecessorIterable,
{
    type Alphabet = Ts::Alphabet;

    type StateIndex = Ts::StateIndex;

    type StateColor = Ts::StateColor;

    type EdgeColor = Ts::EdgeColor;

    type EdgeRef<'this>
        = Reversed<Ts::PreEdgeRef<'this>>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = std::iter::Map<
        Ts::EdgesToIter<'this>,
        fn(Ts::PreEdgeRef<'this>) -> Reversed<Ts::PreEdgeRef<'this>>,
    >
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.0.alphabet()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(self.0.predecessors(state)?.map(Reversed))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.0.state_color(state)
    }

    fn state_bound(&self) -> Option<usize> {
        self.0.state_bound()
    }
}

impl<Ts> States for Reversed<Ts>
where
    Ts: PredecessorIterable + States,
{
    type StatesIter<'this>
        = Ts::StatesIter<'this>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        self.0.states()
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        self.0.contains_state(index)
    }

    fn state_count(&self) -> usize {
        self.0.state_count()
    }
}

impl<Ts> PredecessorIterable for Reversed<Ts>
where
    Ts: TransitionSystem + PredecessorIterable,
{
    type PreEdgeRef<'this>
        = Reversed<Ts::EdgeRef<'this>>
    where
        Self: 'this;

    type EdgesToIter<'this>
        = std::iter::Map<
        Ts::EdgesFromIter<'this>,
        fn(Ts::EdgeRef<'this>) -> Reversed<Ts::EdgeRef<'this>>,
    >
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Some(self.0.edges_from(state)?.map(Reversed))
    }
}
