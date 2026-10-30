use crate::TransitionSystem;
use crate::alphabet::Alphabet;
use crate::ts::EdgeOf;
use crate::ts::{EdgeExpression, StateIndex, SymbolOf, operations};

/// Implementors of this trait are [`TransitionSystem`]s which allow iterating over the predecessors of a state.
pub trait PredecessorIterable: TransitionSystem {
    /// The type of iterator over the predecessors of a state.
    type EdgesToIter<'this>: Iterator<Item = EdgeOf<'this, Self>>
    where
        Self: 'this;

    /// Returns an iterator over the predecessors of the given state. If the state is not in the transition system, this returns `None`.
    ///
    /// # Example
    /// ```
    /// use automata::ts::{PredecessorIterable, Builder};
    ///
    /// let ts = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (2, 'a', 0)])
    ///     .build_dts();
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
    type EdgesToIter<'this>
        = Ts::EdgesToIter<'this>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Ts::predecessors(self, state)
    }
}
impl<Ts: PredecessorIterable> PredecessorIterable for &mut Ts {
    type EdgesToIter<'this>
        = Ts::EdgesToIter<'this>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Ts::predecessors(self, state)
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
    type EdgesToIter<'this>
        = operations::ProductEdgesTo<'this, L, R>
    where
        Self: 'this;
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        operations::ProductEdges::new_to(&self.0, &self.1, state)
    }
}

#[cfg(test)]
mod tests {
    use crate::ts::Builder;
    use crate::ts::predecessors::PredecessorIterable;

    #[test]
    fn predecessor_iterable() {
        let ts = Builder::without_state_colors()
            .with_transitions([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (2, 'a', 0)])
            .build_dts();
        let mut predecessors = ts.predecessors(0).unwrap().collect::<Vec<_>>();
        predecessors.sort_by_key(|e| e.source());
        assert_eq!(
            predecessors,
            vec![(0, 'b', 0), (1, 'a', 0), (2u32, 'a', 0u32)]
        );
    }
}
