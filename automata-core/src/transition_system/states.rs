use crate::innerlude::*;

use super::{color::Weak, petgraph::GraphTsStateReference};

pub trait States: TransitionSystemBase {
    type StateIndex: IdType;
    type StateColor: Color;

    type StateRef<'this>: StateReference<'this, StateIndex<Self>, StateColor<Self>>
    where
        Self: 'this;

    fn q(&self, idx: StateIndex<Self>) -> Option<Self::StateRef<'_>>;
}

impl<T: States> States for &T {
    type StateColor = T::StateColor;
    type StateIndex = T::StateIndex;
    type StateRef<'this> = T::StateRef<'this> where Self: 'this;
    fn q(&self, idx: StateIndex<Self>) -> Option<Self::StateRef<'_>> {
        T::q(self, idx)
    }
}

pub trait StateReference<'a, Idx: IdType, Q: Color> {
    fn state_index(&self) -> Idx;
    fn color(&self) -> Weak<'_, Q>;
}

impl<'a, Q: Color, Idx: IdType> StateReference<'a, Idx, Q> for &'a (Idx, Q) {
    fn color(&self) -> Weak<'_, Q> {
        Weak::Borrowed(&self.1)
    }
    fn state_index(&self) -> Idx {
        self.0
    }
}

impl<'a, Q: Color, Idx: IdType> StateReference<'a, Idx, Q> for (Idx, &'a Q) {
    fn color(&self) -> Weak<'_, Q> {
        Weak::Borrowed(&self.1)
    }
    fn state_index(&self) -> Idx {
        self.0
    }
}

impl<A: Alphabet, Q: Color, C: Color, const DET: bool> States for GraphTs<A, Q, C, DET> {
    type StateColor = Q;
    type StateIndex = DefaultIdType;
    type StateRef<'this> = GraphTsStateReference<'this, StateColor<Self>> where Self: 'this;
    fn q(&self, idx: StateIndex<Self>) -> Option<Self::StateRef<'_>> {
        Some(GraphTsStateReference::new(
            idx,
            self.graph()
                .node_weight(petgraph::stable_graph::node_index(idx as usize))?,
        ))
    }
}

pub trait StateIterable: States {
    type StatesIter<'this>: Iterator<Item = Self::StateRef<'this>>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_>;
}

impl<T: StateIterable> StateIterable for &T {
    type StatesIter<'this> = T::StatesIter<'this> where Self: 'this;

    fn states(&self) -> T::StatesIter<'_> {
        T::states(self)
    }
}
