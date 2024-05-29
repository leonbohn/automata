use crate::innerlude::*;

use super::StateColor;

pub trait StateReference<'a, Idx: IdType, Q: Color> {
    fn state_index(&self) -> Idx;
    fn color(&self) -> &'a Q;
}

impl<'a, Q: Color, Idx: IdType> StateReference<'a, Idx, Q> for &'a (Idx, Q) {
    fn color(&self) -> &'a Q {
        &self.1
    }
    fn state_index(&self) -> Idx {
        self.0
    }
}

impl<'a, Q: Color, Idx: IdType> StateReference<'a, Idx, Q> for (Idx, &'a Q) {
    fn color(&self) -> &'a Q {
        self.1
    }
    fn state_index(&self) -> Idx {
        self.0
    }
}

pub trait StateIterable: TransitionSystemBase {
    type StateRef<'this>: StateReference<'this, StateIndex<Self>, StateColor<Self>>
    where
        Self: 'this;
    type StatesIter<'this>: Iterator<Item = Self::StateRef<'this>>
    where
        Self: 'this;

    fn q(&self, idx: StateIndex<Self>) -> Option<Self::StateRef<'_>>;
    fn states(&self) -> Self::StatesIter<'_>;
}

impl<T: StateIterable> StateIterable for &T {
    type StateRef<'this> = T::StateRef<'this> where Self: 'this;
    type StatesIter<'this> = T::StatesIter<'this> where Self: 'this;
    fn q(&self, idx: StateIndex<Self>) -> Option<Self::StateRef<'_>> {
        T::q(self, idx)
    }
    fn states(&self) -> Self::StatesIter<'_> {
        T::states(self)
    }
}
