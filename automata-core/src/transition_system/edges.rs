use crate::innerlude::*;

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
    type EdgeRef<'this>: EdgeReference<'this, StateIndex<Self>, Expression<Self>, EdgeColor<Self>>
    where
        Self: 'this;
    type EdgesFromIter<'this>: Iterator<Item = Self::EdgeRef<'this>>
    where
        Self: 'this;
    fn edges_from(&self, source: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>>;
}
