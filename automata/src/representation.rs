#![allow(missing_docs)]

use operations::MapStateColor;

use crate::prelude::*;

pub trait StateColored<Q: Color = Int> {}
impl<T: TransitionSystem> StateColored<StateColor<T>> for T {}

pub trait EdgeColored<C: Color = Int> {}
impl<T: TransitionSystem> EdgeColored<EdgeColor<T>> for T {}

pub trait CollectTs: TransitionSystem {
    fn collect_dts(&self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
        self.collect_dts_preserving().unzip_state_color()
    }
    fn collect_dts_and_initial(
        &self,
    ) -> (
        DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>,
        DefaultIdType,
    )
    where
        Self: Pointed,
    {
        let old_initial = self.initial();
        let preserving = self.collect_dts_preserving();
        let new_initial = preserving
            .state_indices_with_color()
            .find_map(|(new_idx, (old_idx, _))| {
                if old_idx == old_initial {
                    Some(new_idx)
                } else {
                    None
                }
            })
            .expect("old initial state did not exist");
        (preserving.unzip_state_color(), new_initial)
    }
    fn collect_dts_preserving(
        &self,
    ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
        todo!()
    }
    /// Collects into a transition system of type `Ts`, but only considers states that
    /// are reachable from the initial state. Naturally, this means that `self` must
    /// be a pointed transition system.
    #[allow(clippy::type_complexity)]
    fn trim_collect_pointed(
        &self,
    ) -> (
        DTS<Self::Alphabet, Self::StateColor, Self::EdgeColor>,
        DefaultIdType,
    )
    where
        Self: Pointed,
    {
        let reachable_indices = self.reachable_state_indices().collect::<math::Set<_>>();
        let restricted = self.restrict_state_indices(|idx| reachable_indices.contains(&idx));
        restricted.collect_dts_and_initial()
    }

    fn collect_dfa(&self) -> DFA<Self::Alphabet>
    where
        Self: Pointed,
    {
        todo!()
    }

    fn collect_moore(&self) -> MooreMachine<Self::Alphabet, StateColor<Self>>
    where
        Self: Pointed,
    {
        todo!()
    }
    fn collect_mealy(&self) -> MealyMachine<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>
    where
        Self: Pointed,
    {
        todo!()
    }
    fn collect_dba(&self) -> DBA<Self::Alphabet>
    where
        Self: Pointed,
    {
        todo!()
    }
    fn collect_dpa(&self) -> DPA<Self::Alphabet>
    where
        Self: Pointed,
    {
        todo!()
    }
    fn collect_right_congruence(
        &self,
    ) -> RightCongruence<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>
    where
        Self: Pointed,
    {
        todo!()
    }
}
impl<Ts: TransitionSystem> CollectTs for Ts {}

pub trait IntoTs: TransitionSystem {
    fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
        self.into_dts_preserving().unzip_state_color()
    }

    fn into_dts_and_initial(
        self,
    ) -> (
        DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>,
        DefaultIdType,
    )
    where
        Self: Pointed,
    {
        let old_initial = self.initial();
        let preserving = self.into_dts_preserving();
        let new_initial = preserving
            .state_indices_with_color()
            .find_map(|(new_idx, (old_idx, _))| {
                if old_idx == old_initial {
                    Some(new_idx)
                } else {
                    None
                }
            })
            .expect("old initial state did not exist");
        (preserving.unzip_state_color(), new_initial)
    }

    #[allow(clippy::type_complexity)]
    fn into_dts_preserving(
        self,
    ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>>;

    fn into_moore(self) -> MooreMachine<Self::Alphabet, StateColor<Self>>
    where
        Self: Pointed,
    {
        let initial = self.initial();
        self.into_moore_with_initial(initial)
    }

    fn into_moore_with_initial(
        self,
        state: StateIndex<Self>,
    ) -> MooreMachine<Self::Alphabet, StateColor<Self>> {
        let (ts, initial) = self.with_initial(state).into_dts_and_initial();
        assert!(ts.size() > 0);
        MooreMachine::from_parts(ts.linked_map_edges(|_, e, _, _| (e, Void)), initial)
    }
    fn into_mealy(self) -> MealyMachine<Self::Alphabet, Void, EdgeColor<Self>> {
        let ts = self.into_dts().linked_map_states(|_, _| Void);
        assert!(ts.size() > 0);
        MealyMachine::from_parts(ts, 0)
    }

    /// Collects the transition system representing `self` and builds a new [`DFA`].
    fn into_dfa_with_initial(self, initial: StateIndex<Self>) -> DFA<Self::Alphabet>
    where
        Self: Congruence<StateColor = bool>,
    {
        let (dts, initial) = self
            .with_initial(initial)
            .erase_edge_colors()
            .into_dts_and_initial();
        DFA::from_parts(dts, initial)
    }

    fn into_dfa(self) -> DFA<Self::Alphabet>
    where
        Self: Pointed + Congruence<StateColor = bool>,
    {
        let initial = self.initial();
        self.into_dfa_with_initial(initial)
    }

    /// Collects the transition system representing `self` and builds a new [`DPA`].
    fn into_dpa_with_initial(self, initial: StateIndex<Self>) -> DPA<Self::Alphabet>
    where
        Self: Deterministic<EdgeColor = Int>,
    {
        let (ts, initial) = self
            .with_initial(initial)
            .erase_state_colors()
            .into_dts_and_initial();
        DPA::from_parts(ts, initial)
    }

    /// Collects the transition system representing `self` and builds a new [`DPA`].
    fn into_dpa(self) -> DPA<Self::Alphabet>
    where
        Self: Congruence<EdgeColor = Int>,
    {
        let initial = self.initial();
        self.into_dpa_with_initial(initial)
    }

    /// Collects the transition system representing `self` and builds a new [`DBA`].
    fn into_dba_with_initial(self, initial: StateIndex<Self>) -> DBA<Self::Alphabet>
    where
        Self: Deterministic<EdgeColor = bool>,
    {
        let (ts, initial) = self
            .with_initial(initial)
            .erase_state_colors()
            .into_dts_and_initial();
        DBA::from_parts(ts, initial)
    }

    /// Collects the transition system representing `self` and builds a new [`DPA`].
    fn into_dba(self) -> DBA<Self::Alphabet>
    where
        Self: Congruence<EdgeColor = bool>,
    {
        let initial = self.initial();
        self.into_dba_with_initial(initial)
    }

    /// Creates a new instance of a [`RightCongruence`] from the transition structure of `self`.
    /// Note, that this method might not preserve state indices!
    fn into_right_congruence(
        self,
    ) -> RightCongruence<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>
    where
        Self: Deterministic + Pointed,
    {
        let (ts, initial) = self.into_dts_and_initial();
        RightCongruence::from_parts(ts, initial)
    }
}

mod impl_into_ts {
    use super::*;

    impl<A: Alphabet, Q: Color, C: Color> IntoTs for DTS<A, Q, C> {
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), C> {
            self.zip_state_indices()
        }
        fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, C> {
            self
        }
    }
    impl<T: IntoTs, C: Color, F> IntoTs for operations::MapEdgeColor<T, F>
    where
        F: Fn(EdgeColor<T>) -> C,
    {
        fn into_dts_preserving(self) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<T>), C> {
            let (ts, f) = self.into_parts();
            ts.into_dts_preserving()
                .linked_map_edges(|_, e, c, _| (e, f(c)))
        }
        fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
            let (ts, f) = self.into_parts();
            ts.into_dts().linked_map_edges(|_, e, c, _| (e, f(c)))
        }
    }
    impl<T: IntoTs, Q: Color, F> IntoTs for MapStateColor<T, F>
    where
        T: TransitionSystem,
        F: Fn(T::StateColor) -> Q,
    {
        fn into_dts(self) -> DTS<Self::Alphabet, Q, EdgeColor<Self>> {
            let (ts, f) = self.into_parts();
            ts.into_dts().linked_map_states(|_, c| f(c))
        }
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
            let (ts, f) = self.into_parts();
            ts.into_dts_preserving()
                .linked_map_states(|_, (i, c)| (i, f(c)))
        }
    }
    impl<T: IntoTs, F> IntoTs for operations::RestrictByStateIndex<T, F>
    where
        F: operations::StateIndexFilter<T::StateIndex>,
    {
        fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
            self.into_dts_preserving().unzip_state_color()
        }
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
            // let (ts, f) = self.into_parts();
            // ts.into_dts_preserving()
            //     .graphts_restrict_states(|_, (i, _)| f.is_unmasked(*i))
            todo!()
        }
    }
    impl<Ts: IntoTs, P: operations::ProvidesStateColor<Ts::StateIndex>> IntoTs
        for operations::WithStateColor<Ts, P>
    {
        fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
            self.into_dts_preserving().unzip_state_color()
        }
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
            // let (ts, p) = self.into_parts();
            // ts.into_dts_preserving()
            //     .graphts_map_state_color(|(i, _)| (i, p.state_color(i)))
            todo!()
        }
    }
    impl<T, D, F> IntoTs for operations::MapEdges<T, F>
    where
        T: IntoTs,
        D: Color,
        F: Fn(StateIndex<T>, &EdgeExpression<T>, EdgeColor<T>, StateIndex<T>) -> D,
    {
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
            todo!()
        }
    }

    impl<L, R> IntoTs for operations::MatchingProduct<L, R>
    where
        L: IntoTs,
        R: IntoTs,
        R::Alphabet: Alphabet<Symbol = SymbolOf<L>, Expression = EdgeExpression<L>>,
        L::StateColor: Clone,
        R::StateColor: Clone,
    {
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
            todo!()
        }
    }
    impl<Z, D, const OMEGA: bool> IntoTs
        for Automaton<D::Alphabet, Z, StateColor<D>, EdgeColor<D>, D, OMEGA>
    where
        D: IntoTs,
    {
        fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
            self.ts.into_dts()
        }
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
            self.ts.into_dts_preserving()
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn representation() {
        use crate::prelude::*;
        let ts = TSBuilder::default()
            .with_state_colors([false, false, true, true, true, false])
            .with_edges([
                (0, 'a', 9, 1),
                (0, 'b', 1, 2),
                (1, 'a', 2, 0),
                (1, 'b', 1, 3),
                (2, 'a', 4, 4),
                (2, 'b', 1, 5),
                (3, 'a', 2, 4),
                (3, 'b', 2, 5),
                (4, 'a', 1, 4),
                (4, 'b', 1, 5),
                (5, 'a', 2, 5),
                (5, 'b', 1, 5),
            ])
            .into_dts();
        let moore = ts.clone().into_moore_with_initial(0);
        let mealy = ts.into_mealy();
        assert_eq!(moore.size(), mealy.size());
        assert_eq!(moore.initial(), mealy.initial());
    }
}
