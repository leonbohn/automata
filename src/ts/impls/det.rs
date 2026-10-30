use std::borrow::Cow;

use crate::TransitionSystem;
use crate::alphabet::Alphabet;
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{EdgeId, EdgeTuple, ForAlphabet, Shrinkable, StateColor, StateIndex, States};

/// Makes the determinism of a transition system part of its type.
///
/// `Det<T>` wraps a transition system `T` that has at most one edge per state and symbol, and keeps
/// it that way: adding an edge that overlaps with existing edges **replaces** them, see
/// [`Sproutable::add_edge`](crate::ts::Sproutable::add_edge). A `Det<T>` is created empty with
/// [`ForAlphabet`], by the [`Builder`](crate::ts::Builder), or from an existing system with
/// [`Det::try_new`], which checks the property.
///
/// Used as a marker, `Det<Linked>` is the [`Storage`](crate::ts::Storage) whose systems are
/// `Det<LinkedTs<A, Q, C>>`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Det<T>(pub(crate) T);

impl<T> Det<T> {
    /// The system that is wrapped.
    pub fn inner(&self) -> &T {
        &self.0
    }

    /// Forgets that the system is deterministic.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T: States> Det<T> {
    /// Wraps `ts` if it is deterministic and returns it as the error otherwise.
    pub fn try_new(ts: T) -> Result<Self, T> {
        if ts.is_deterministic() {
            Ok(Self(ts))
        } else {
            Err(ts)
        }
    }
}

impl<T: TransitionSystem> TransitionSystem for Det<T> {
    type Alphabet = T::Alphabet;
    type StateIndex = T::StateIndex;
    type StateColor = T::StateColor;
    type EdgeColor = T::EdgeColor;
    type EdgesFromIter<'this>
        = T::EdgesFromIter<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.0.alphabet()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        self.0.edges_from(state)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.0.state_color(state)
    }

    fn state_bound(&self) -> Option<usize> {
        self.0.state_bound()
    }
}

impl<T: States> States for Det<T> {
    type StatesIter<'this>
        = T::StatesIter<'this>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        self.0.states()
    }

    fn state_count(&self) -> usize {
        self.0.state_count()
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        self.0.contains_state(index)
    }
}

impl<T: PredecessorIterable> PredecessorIterable for Det<T> {
    type EdgesToIter<'this>
        = T::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        self.0.predecessors(state)
    }
}

impl<A: Alphabet, T: ForAlphabet<A>> ForAlphabet<A> for Det<T> {
    fn for_alphabet(from: A) -> Self {
        Self(T::for_alphabet(from))
    }

    fn for_alphabet_size_hint(from: A, size_hint: usize) -> Self {
        Self(T::for_alphabet_size_hint(from, size_hint))
    }
}

impl<T: Shrinkable> Shrinkable for Det<T> {
    fn remove_edge(&mut self, id: EdgeId) -> Option<EdgeTuple<Self>> {
        self.0.remove_edge(id)
    }

    fn out_edge_ids(
        &self,
        source: StateIndex<Self>,
        keep: impl for<'e> FnMut(&crate::ts::EdgeOf<'e, Self>) -> bool,
    ) -> Option<Vec<crate::ts::EdgeId>> {
        self.0.out_edge_ids(source, keep)
    }

    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<StateColor<Self>> {
        self.0.remove_state(state)
    }

    fn remove_edges_to(&mut self, target: StateIndex<Self>) -> Option<Vec<EdgeTuple<Self>>> {
        self.0.remove_edges_to(target)
    }
}
