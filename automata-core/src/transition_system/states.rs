use crate::innerlude::*;

use super::StateColor;

pub trait StateReference<'a, Q: Color, Idx: IdType = DefaultIdType> {
    fn state_index(&self) -> Idx;
    fn color(&self) -> &'a Q;
}

impl<'a, Q: Color, Idx: IdType> StateReference<'a, Q, Idx> for &'a (Q, Idx) {
    fn color(&self) -> &'a Q {
        &self.0
    }
    fn state_index(&self) -> Idx {
        self.1
    }
}

impl<'a, Q: Color, Idx: IdType> StateReference<'a, Q, Idx> for (&'a Q, Idx) {
    fn color(&self) -> &'a Q {
        self.0
    }
    fn state_index(&self) -> Idx {
        self.1
    }
}

pub trait StateIterable: TransitionSystemBase {
    type StateReference<'this>: StateReference<'this, StateColor<Self>, StateIndex<Self>>
    where
        Self: 'this;

    fn state(&self, idx: StateIndex<Self>) -> Self::StateReference<'_>;
}

impl<T: StateIterable> StateIterable for &T {
    type StateReference<'this> = T::StateReference<'this> where Self: 'this;
    fn state(&self, idx: StateIndex<Self>) -> Self::StateReference<'_> {
        T::state(self, idx)
    }
}
