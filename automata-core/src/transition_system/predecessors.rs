use crate::innerlude::*;

/// Implementors of this trait are [`TransitionSystem`]s which allow iterating over the predecessors of a state.
pub trait PredecessorIterable: TransitionSystemBase {
    /// The type of iterator over the predecessors of a state.
    type EdgesToIter<'this>: Iterator<Item = Self::EdgeRef<'this>>
    where
        Self: 'this;

    /// Returns an iterator over the predecessors of the given state. If the state is not in the transition system, this returns `None`.
    ///
    /// # Example
    /// ```
    /// use automata::prelude::*;
    ///
    /// let ts = TSBuilder::without_state_colors()
    ///     .with_transitions([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (2, 'a', 0)])
    ///     .into_dts();
    /// assert_eq!(ts.predecessors(0).unwrap().collect::<Vec<_>>().len(), 3);
    /// ```
    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>>;
}

#[cfg(test)]
mod tests {
    #[test]
    fn predecessor_iterable() {
        use crate::innerlude::*;

        let ts = TSBuilder::without_state_colors()
            .with_transitions([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (2, 'a', 0)])
            .into_dts();
        assert_eq!(
            ts.predecessors(0).unwrap().collect::<Vec<_>>(),
            vec![(2, 'a', 0), (1, 'a', 0), (0, 'b', 0)]
        );
    }
}
