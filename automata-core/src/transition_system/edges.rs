use crate::innerlude::*;

pub trait IntoEdgeTuple<T: TransitionSystemBase> {
    fn into_tuple(self) -> (StateIndex<T>, Expression<T>, EdgeColor<T>, StateIndex<T>);
}

impl<T: TransitionSystemBase> IntoEdgeTuple<T>
    for (StateIndex<T>, Expression<T>, EdgeColor<T>, StateIndex<T>)
{
    fn into_tuple(self) -> (StateIndex<T>, Expression<T>, EdgeColor<T>, StateIndex<T>) {
        self
    }
}
impl<T: TransitionSystemBase<EdgeColor = Void>> IntoEdgeTuple<T>
    for (StateIndex<T>, Expression<T>, StateIndex<T>)
{
    fn into_tuple(self) -> (StateIndex<T>, Expression<T>, EdgeColor<T>, StateIndex<T>) {
        (self.0, self.1, Void, self.2)
    }
}

pub trait EdgeReference<'a, Idx: IdType, E: AlphabetExpression, C: Color> {
    fn source(&self) -> Idx;
    fn target(&self) -> Idx;
    fn expression(&self) -> &'a E;
    fn color(&self) -> &'a C;
}

impl<'a, Idx: IdType, E: AlphabetExpression, C: Color> EdgeReference<'a, Idx, E, C>
    for (Idx, &'a E, &'a C, Idx)
{
    fn source(&self) -> Idx {
        self.0
    }
    fn target(&self) -> Idx {
        self.3
    }
    fn expression(&self) -> &'a E {
        self.1
    }
    fn color(&self) -> &'a C {
        self.2
    }
}
impl<'a, Idx: IdType, E: AlphabetExpression, C: Color> EdgeReference<'a, Idx, E, C>
    for &'a (Idx, E, C, Idx)
{
    fn source(&self) -> Idx {
        self.0
    }
    fn target(&self) -> Idx {
        self.3
    }
    fn expression(&self) -> &'a E {
        &self.1
    }
    fn color(&self) -> &'a C {
        &self.2
    }
}

pub trait EdgesFrom: TransitionSystemBase {
    type EdgesFromIter<'this>: Iterator<Item = Self::EdgeRef<'this>>
    where
        Self: 'this;
    fn edges_from(&self, source: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>>;
}
