use crate::prelude::*;

use super::EdgeReference;

/// Implementors of this trait are [`TransitionSystem`]s which allow iterating over the predecessors of a state.
pub trait PredecessorIterable: TransitionSystem {
    /// The type of pre-transition that the iterator yields.
    type PreEdgeRef<'this>: IsEdge<'this, EdgeExpression<Self>, Self::StateIndex, EdgeColor<Self>>
    where
        Self: 'this;

    /// The type of iterator over the predecessors of a state.
    type EdgesToIter<'this>: Iterator<Item = Self::PreEdgeRef<'this>>
    where
        Self: 'this;

    /// Returns an iterator over the predecessors of the given `state`. Returns `None` if the state does not exist.
    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>>;

    /// Reverses the directions of all transitions in the transition system. This consumes the transition system.
    /// See also [`operations::Reversed`].
    fn reversed(self) -> operations::Reversed<Self> {
        operations::Reversed(self)
    }
}

impl<Ts, F> PredecessorIterable for operations::RestrictByStateIndex<Ts, F>
where
    Ts: PredecessorIterable,
    F: operations::StateIndexFilter<Ts::StateIndex>,
{
    type PreEdgeRef<'this> = Ts::PreEdgeRef<'this> where Self: 'this;
    type EdgesToIter<'this> = operations::RestrictedEdgesToIter<'this, Ts, F> where Self: 'this;
    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        Some(operations::RestrictedEdgesToIter::new(
            self.ts().predecessors(state.to_index(self)?)?,
            self.filter(),
        ))
    }
}

impl<Ts: PredecessorIterable> PredecessorIterable for &Ts {
    type PreEdgeRef<'this> = Ts::PreEdgeRef<'this> where Self: 'this;
    type EdgesToIter<'this> = Ts::EdgesToIter<'this> where Self: 'this;
    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        Ts::predecessors(self, state.to_index(self)?)
    }
}
impl<Ts: PredecessorIterable> PredecessorIterable for &mut Ts {
    type PreEdgeRef<'this> = Ts::PreEdgeRef<'this> where Self: 'this;
    type EdgesToIter<'this> = Ts::EdgesToIter<'this> where Self: 'this;
    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        Ts::predecessors(self, state.to_index(self)?)
    }
}

impl<D, Ts, F> PredecessorIterable for operations::MapEdgeColor<Ts, F>
where
    D: Color,
    Ts: PredecessorIterable,
    F: Fn(Ts::EdgeColor) -> D,
{
    type PreEdgeRef<'this> = operations::MappedPreTransition<Ts::PreEdgeRef<'this>, &'this F, Ts::EdgeColor> where Self: 'this;
    type EdgesToIter<'this> = operations::MappedTransitionsToIter<'this, Ts::EdgesToIter<'this>, F, Ts::EdgeColor> where Self: 'this;
    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        Some(operations::MappedTransitionsToIter::new(
            self.ts().predecessors(state.to_index(self)?)?,
            self.f(),
        ))
    }
}

impl<D, Ts, F> PredecessorIterable for operations::MapStateColor<Ts, F>
where
    D: Color,
    Ts: PredecessorIterable,
    F: Fn(Ts::StateColor) -> D,
{
    type EdgesToIter<'this> = Ts::EdgesToIter<'this> where Self: 'this;
    type PreEdgeRef<'this> = Ts::PreEdgeRef<'this> where Self: 'this;
    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        self.ts().predecessors(state.to_index(self)?)
    }
}

impl<L, R> PredecessorIterable for operations::MatchingProduct<L, R>
where
    L: PredecessorIterable,
    R: PredecessorIterable,
    R::Alphabet: Alphabet<Symbol = SymbolOf<L>, Expression = EdgeExpression<L>>,
    L::StateColor: Clone,
    R::StateColor: Clone,
{
    type PreEdgeRef<'this> = operations::ProductPreTransition<'this, L::StateIndex, R::StateIndex, EdgeExpression<L>, L::EdgeColor, R::EdgeColor> where Self: 'this;
    type EdgesToIter<'this> = operations::ProductEdgesTo<'this, L, R> where Self: 'this;
    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        operations::ProductEdgesTo::new(&self.0, &self.1, state.to_index(self)?)
    }
}

impl<A: Alphabet, Q: Color, C: Color> PredecessorIterable for EdgeLists<A, Q, C> {
    type PreEdgeRef<'this> = EdgeReference<'this, A::Expression, usize, C> where Self: 'this;
    type EdgesToIter<'this> = BTSPredecessors<'this, A, C>
    where
        Self: 'this;
    fn predecessors<Idx: Indexes<Self>>(&self, _state: Idx) -> Option<Self::EdgesToIter<'_>> {
        unimplemented!("Due to a recent change in the implementation of `MutableTs`, this method is not yet implemented.")
    }
}

/// Iterator over the predecessors of a state in a BTS.
#[derive(Clone)]
pub struct BTSPredecessors<'a, A: Alphabet, C: Color> {
    it: std::slice::Iter<'a, (usize, A::Expression, C)>,
    state: usize,
}

impl<'a, A: Alphabet, C: Color> Iterator for BTSPredecessors<'a, A, C> {
    type Item = EdgeReference<'a, A::Expression, usize, C>;

    fn next(&mut self) -> Option<Self::Item> {
        self.it
            .next()
            .map(|(s, e, c)| EdgeReference::new(*s, e, c, self.state))
    }
}

impl<'a, A: Alphabet, C: Color> BTSPredecessors<'a, A, C> {
    /// Creates a new instance from an iterator and a state.
    pub fn new(it: std::slice::Iter<'a, (usize, A::Expression, C)>, state: usize) -> Self {
        Self { it, state }
    }
}
