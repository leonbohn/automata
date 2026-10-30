use crate::representation::{IntoTransitions, Parts, materialize};
use crate::ts::EdgeOf;
use crate::ts::SymbolOf;
use crate::ts::{Bfs, Deterministic, Pointed, StateIndex, StateSet, States, TransitionSystem};
use std::borrow::Cow;

/// The part of a [`Pointed`] transition system that is reachable from its initial state, see
/// [`Pointed::reachable_part`].
///
/// Implicit transition systems like [`super::SubsetConstruction`] or [`super::MatchingProduct`]
/// do not implement [`States`] as they cannot cheaply enumerate their states. This adapter
/// explores everything that is reachable once, when it is created, and from then on provides
/// [`States`] with O(1) [`States::contains_state`].
#[derive(Debug, Clone)]
pub struct ReachablePart<Ts: TransitionSystem> {
    ts: Ts,
    initial: Ts::StateIndex,
    /// The reachable states in the order in which they were discovered.
    states: Vec<Ts::StateIndex>,
    reachable: StateSet<Ts::StateIndex>,
}

impl<Ts: Pointed> ReachablePart<Ts> {
    /// Explores all states that are reachable from the initial state of `ts`.
    pub fn new(ts: Ts) -> Self {
        let initial = ts.initial();
        let states: Vec<_> = Bfs::new(&ts, initial).collect();
        let mut reachable = StateSet::new(ts.state_bound());
        reachable.extend(states.iter().copied());
        Self {
            ts,
            initial,
            states,
            reachable,
        }
    }
}

impl<Ts: TransitionSystem> TransitionSystem for ReachablePart<Ts> {
    type Alphabet = Ts::Alphabet;
    type StateIndex = Ts::StateIndex;
    type StateColor = Ts::StateColor;
    type EdgeColor = Ts::EdgeColor;
    type EdgesFromIter<'this>
        = Ts::EdgesFromIter<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        if self.reachable.contains(&state) {
            self.ts.edges_from(state)
        } else {
            None
        }
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        if self.reachable.contains(&state) {
            self.ts.state_color(state)
        } else {
            None
        }
    }

    fn state_bound(&self) -> Option<usize> {
        self.ts.state_bound()
    }
}

impl<Ts: TransitionSystem> States for ReachablePart<Ts> {
    type StatesIter<'this>
        = std::iter::Copied<std::slice::Iter<'this, Ts::StateIndex>>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        self.states.iter().copied()
    }

    fn state_count(&self) -> usize {
        self.states.len()
    }

    fn contains_state(&self, state: Ts::StateIndex) -> bool {
        self.reachable.contains(&state)
    }
}

/// The states and edges are computed (and cloned) up front, since the system may be lazy and
/// borrow from the wrapped one.
impl<Ts: TransitionSystem> IntoTransitions for ReachablePart<Ts> {
    type Initial = Ts::StateIndex;
    type IntoStates = std::vec::IntoIter<(Ts::StateIndex, Ts::StateColor)>;
    type IntoEdges = std::vec::IntoIter<crate::representation::OwnedEdge<Ts>>;

    fn into_transitions(
        self,
    ) -> Parts<Ts::Alphabet, Self::IntoStates, Self::IntoEdges, Ts::StateIndex> {
        let (states, edges) = materialize(&self.ts, self.states.iter().copied());
        Parts {
            alphabet: self.ts.alphabet().clone(),
            states,
            edges,
            initial: self.initial,
        }
    }
}

impl<Ts: TransitionSystem> Pointed for ReachablePart<Ts> {
    fn initial(&self) -> Self::StateIndex {
        self.initial
    }
}

impl<Ts: Deterministic> Deterministic for ReachablePart<Ts> {
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        if self.reachable.contains(&state) {
            self.ts.edge(state, symbol)
        } else {
            None
        }
    }
}
