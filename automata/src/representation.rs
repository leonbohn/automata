#![allow(missing_docs)]

use operations::MapStateColor;

use crate::prelude::*;

pub trait StateColored<Q: Color = Int> {}
impl<T: TransitionSystem> StateColored<StateColor<T>> for T {}

pub trait EdgeColored<C: Color = Int> {}
impl<T: TransitionSystem> EdgeColored<EdgeColor<T>> for T {}

pub trait IntoDts: TransitionSystem {
    fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
        self.into_dts_preserving().unzip_state_indices()
    }

    #[allow(clippy::type_complexity)]
    fn into_dts_preserving(
        self,
    ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>>;

    fn into_moore(self) -> MooreMachine<Self::Alphabet, StateColor<Self>> {
        let ts = self.into_dts().graphts_map_edge_color(|_| Void);
        assert!(ts.size() > 0);
        MooreMachine::from_parts(ts, 0)
    }
    fn into_mealy(self) -> MealyMachine<Self::Alphabet, Void, EdgeColor<Self>> {
        let ts = self.into_dts().graphts_map_state_color(|_| Void);
        assert!(ts.size() > 0);
        MealyMachine::from_parts(ts, 0)
    }

    fn clone_dts(&self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>
    where
        Self: Clone,
    {
        self.clone().into_dts()
    }
    fn clone_moore(&self) -> MooreMachine<Self::Alphabet, StateColor<Self>>
    where
        Self: Clone,
    {
        self.clone().into_moore()
    }
    fn clone_mealy(&self) -> MealyMachine<Self::Alphabet, Void, EdgeColor<Self>>
    where
        Self: Clone,
    {
        self.clone().into_mealy()
    }
}

mod impls {
    use super::*;

    impl<A: Alphabet, Q: Color, C: Color> IntoDts for DTS<A, Q, C> {
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), C> {
            self.zip_state_indices()
        }
        fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, C> {
            self
        }
    }
    impl<T: IntoDts, C: Color, F> IntoDts for operations::MapEdgeColor<T, F>
    where
        F: Fn(EdgeColor<T>) -> C,
    {
        fn into_dts_preserving(self) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<T>), C> {
            let (ts, f) = self.into_parts();
            ts.into_dts_preserving().graphts_map_edge_color(f)
        }
        fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
            let (ts, f) = self.into_parts();
            ts.into_dts().graphts_map_edge_color(f)
        }
    }
    impl<T: IntoDts, Q: Color, F> IntoDts for MapStateColor<T, F>
    where
        T: TransitionSystem,
        F: Fn(T::StateColor) -> Q,
    {
        fn into_dts(self) -> DTS<Self::Alphabet, Q, EdgeColor<Self>> {
            let (ts, f) = self.into_parts();
            ts.into_dts().graphts_map_state_color(f)
        }
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
            let (ts, f) = self.into_parts();
            ts.into_dts_preserving()
                .graphts_map_state_color(|(i, c)| (i, f(c)))
        }
    }
    impl<T: IntoDts, F> IntoDts for operations::RestrictByStateIndex<T, F>
    where
        F: operations::StateIndexFilter<T::StateIndex>,
    {
        fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
            self.into_dts_preserving().unzip_state_indices()
        }
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
            let (ts, f) = self.into_parts();
            ts.into_dts_preserving()
                .graphts_restrict_states(|_, (i, _)| f.is_unmasked(*i))
        }
    }
    impl<Ts: IntoDts, P: operations::ProvidesStateColor<Ts::StateIndex>> IntoDts
        for operations::WithStateColor<Ts, P>
    {
        fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
            self.into_dts_preserving().unzip_state_indices()
        }
        fn into_dts_preserving(
            self,
        ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
            let (ts, p) = self.into_parts();
            ts.into_dts_preserving()
                .graphts_map_state_color(|(i, _)| (i, p.state_color(i)))
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
        let moore = ts.clone_moore();
        let mealy = ts.into_mealy();
        assert_eq!(moore.size(), mealy.size());
        assert_eq!(moore.initial(), mealy.initial());
    }
}
