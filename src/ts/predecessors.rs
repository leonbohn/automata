use crate::TransitionSystem;
use crate::core::Color;
use crate::ts::{EdgeColor, EdgeExpression, IsEdge, StateIndex, SymbolOf, operations};
use automata_core::alphabet::Alphabet;

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

    /// Returns an iterator over the predecessors of the given state. If the state is not in the transition system, this returns `None`.
    ///
    /// # Example
    /// ```
    /// use automata::ts::{PredecessorIterable, TSBuilder};
    ///
    /// let ts = TSBuilder::without_state_colors()
    ///     .with_transitions([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (2, 'a', 0)])
    ///     .into_dts();
    /// assert_eq!(ts.predecessors(0).unwrap().collect::<Vec<_>>().len(), 3);
    /// ```
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>>;

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
    type PreEdgeRef<'this>
        = Ts::PreEdgeRef<'this>
    where
        Self: 'this;
    type EdgesToIter<'this>
        = operations::RestrictedEdgesToIter<'this, Ts, F>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Some(operations::RestrictedEdgesToIter::new(
            self.ts().predecessors(state)?,
            self.filter(),
        ))
    }
}

impl<Ts: PredecessorIterable> PredecessorIterable for &Ts {
    type PreEdgeRef<'this>
        = Ts::PreEdgeRef<'this>
    where
        Self: 'this;
    type EdgesToIter<'this>
        = Ts::EdgesToIter<'this>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Ts::predecessors(self, state)
    }
}
impl<Ts: PredecessorIterable> PredecessorIterable for &mut Ts {
    type PreEdgeRef<'this>
        = Ts::PreEdgeRef<'this>
    where
        Self: 'this;
    type EdgesToIter<'this>
        = Ts::EdgesToIter<'this>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Ts::predecessors(self, state)
    }
}

impl<D, Ts, F> PredecessorIterable for operations::MapEdgeColor<Ts, F>
where
    D: Color,
    Ts: PredecessorIterable,
    F: Fn(Ts::EdgeColor) -> D,
{
    type PreEdgeRef<'this>
        = operations::MappedPreTransition<Ts::PreEdgeRef<'this>, &'this F, Ts::EdgeColor>
    where
        Self: 'this;
    type EdgesToIter<'this>
        = operations::MappedTransitionsToIter<'this, Ts::EdgesToIter<'this>, F, Ts::EdgeColor>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Some(operations::MappedTransitionsToIter::new(
            self.ts().predecessors(state)?,
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
    type EdgesToIter<'this>
        = Ts::EdgesToIter<'this>
    where
        Self: 'this;
    type PreEdgeRef<'this>
        = Ts::PreEdgeRef<'this>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        self.ts().predecessors(state)
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
    type PreEdgeRef<'this>
        = operations::ProductPreTransition<
        'this,
        L::StateIndex,
        R::StateIndex,
        EdgeExpression<L>,
        L::EdgeColor,
        R::EdgeColor,
    >
    where
        Self: 'this;
    type EdgesToIter<'this>
        = operations::ProductEdgesTo<'this, L, R>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        operations::ProductEdgesTo::new(&self.0, &self.1, state)
    }
}

#[cfg(test)]
mod tests {
    use crate::ts::TSBuilder;
    use crate::ts::predecessors::PredecessorIterable;

    #[test]
    fn predecessor_iterable() {
        let ts = TSBuilder::without_state_colors()
            .with_transitions([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (2, 'a', 0)])
            .into_dts();
        assert_eq!(
            ts.predecessors(0).unwrap().collect::<Vec<_>>(),
            vec![(0, 'b', 0), (1, 'a', 0), (2u32, 'a', 0u32)]
        );
    }
}
