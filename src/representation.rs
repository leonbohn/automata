use crate::{Color, Int, Void};
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::automaton::{DBA, DFA, DPA, MealyMachine, MooreMachine};
use crate::ts::{
    DefaultIdType, Deterministic, EdgeColor, ForAlphabet, IsEdge, Sproutable, StateColor,
    StateIndex,
};
use crate::{Congruence, DTS, Pointed, RightCongruence, TransitionSystem};

/// Marker trait for transition systems whose states are colored with `Q`.
pub trait StateColored<Q: Color = Int> {}
impl<T: TransitionSystem> StateColored<StateColor<T>> for T {}

/// Marker trait for transition systems whose edges are colored with `C`.
pub trait EdgeColored<C: Color = Int> {}
impl<T: TransitionSystem> EdgeColored<EdgeColor<T>> for T {}

/// Collects (a reference to) any transition system into a concrete data structure or automaton,
/// which evaluates all lazy operations that are applied to it. The states of the result are
/// numbered `0, 1, ...` in the order of the original indices, so the indices may change.
///
/// The methods with a `_preserving` suffix keep the original index of each state as the first
/// component of its color. Methods that need an initial state are only available for
/// [`Pointed`] transition systems.
#[allow(clippy::type_complexity)]
pub trait CollectTs: TransitionSystem {
    /// Collects into a deterministic transition system; the state indices may change.
    fn collect_dts(&self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
        self.collect_dts_preserving().unzip_state_color()
    }
    /// Collects into a deterministic transition system and returns the index that the initial state
    /// has in the result.
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
    /// Collects into a deterministic transition system whose state colors are pairs of the original
    /// state index and the original color.
    fn collect_dts_preserving(
        &self,
    ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
        let mut out = DTS::for_alphabet_size_hint(self.alphabet().clone(), self.size());
        let mut map = BTreeMap::default();

        for (q, c) in self.state_indices_with_color() {
            map.insert(q, out.add_state((q, c)));
        }
        for q in self.state_indices() {
            for e in self.edges_from(q).unwrap() {
                out.add_edge((
                    *map.get(&e.source()).unwrap(),
                    e.expression().clone(),
                    e.color(),
                    *map.get(&e.target()).unwrap(),
                ));
            }
        }

        debug_assert_eq!(self.size(), out.size());
        out.verify_state();

        out
    }
    /// Collects into a transition system of type `Ts`, but only considers states that
    /// are reachable from the initial state. Naturally, this means that `self` must
    /// be a pointed transition system.
    fn trim_collect_pointed(
        &self,
    ) -> (
        DTS<Self::Alphabet, Self::StateColor, Self::EdgeColor>,
        DefaultIdType,
    )
    where
        Self: Pointed,
    {
        let reachable_indices = self.reachable_state_indices().collect::<BTreeSet<_>>();
        let restricted = self.restrict_state_indices(|idx| reachable_indices.contains(&idx));
        restricted.collect_dts_and_initial()
    }

    /// Collects into a [`DFA`], with the initial state of `self`. Edge colors are dropped.
    fn collect_dfa(&self) -> DFA<Self::Alphabet>
    where
        Self: Pointed<StateColor = bool>,
    {
        let (ts, initial) = self.erase_edge_colors().collect_dts_and_initial();
        DFA::from_parts(ts, initial)
    }

    /// Collects into a [`MooreMachine`], with the initial state of `self`. Edge colors are dropped.
    fn collect_moore(&self) -> MooreMachine<Self::Alphabet, StateColor<Self>>
    where
        Self: Pointed,
    {
        let (ts, initial) = self.erase_edge_colors().collect_dts_and_initial();
        MooreMachine::from_parts(ts, initial)
    }
    /// Collects into a [`MealyMachine`], with the initial state of `self`.
    fn collect_mealy(&self) -> MealyMachine<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>
    where
        Self: Pointed,
    {
        let (ts, initial) = self.collect_dts_and_initial();
        MealyMachine::from_parts(ts, initial)
    }
    /// Collects into a [`DBA`], with the initial state of `self`. State colors are dropped.
    fn collect_dba(&self) -> DBA<Self::Alphabet>
    where
        Self: Pointed<EdgeColor = bool>,
    {
        let (ts, initial) = self.erase_state_colors().collect_dts_and_initial();
        DBA::from_parts(ts, initial)
    }
    /// Collects into a [`DPA`], with the initial state of `self`. State colors are dropped.
    fn collect_dpa(&self) -> DPA<Self::Alphabet>
    where
        Self: Pointed<EdgeColor = Int>,
    {
        let (ts, initial) = self.erase_state_colors().collect_dts_and_initial();
        DPA::from_parts(ts, initial)
    }
    /// Collects into a [`RightCongruence`], with the initial state of `self`.
    fn collect_right_congruence(
        &self,
    ) -> RightCongruence<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>
    where
        Self: Pointed,
    {
        let (ts, initial) = self.collect_dts_and_initial();
        RightCongruence::from_parts(ts, initial)
    }
}
impl<Ts: TransitionSystem> CollectTs for Ts {}

/// Like [`CollectTs`], but consumes the transition system.
#[allow(clippy::type_complexity)]
pub trait IntoTs: TransitionSystem {
    /// Turns `self` into a deterministic transition system; the state indices may change.
    fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
        self.into_dts_preserving().unzip_state_color()
    }

    /// Like [`Self::into_dts_preserving`], additionally returning the new index of the initial state.
    fn into_dts_preserving_and_initial(
        self,
    ) -> (
        DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>>,
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
        (preserving, new_initial)
    }

    /// Like [`Self::into_dts`], additionally returning the new index of the initial state.
    fn into_dts_and_initial(
        self,
    ) -> (
        DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>,
        DefaultIdType,
    )
    where
        Self: Pointed,
    {
        let (preserving, initial) = self.into_dts_preserving_and_initial();
        (preserving.unzip_state_color(), initial)
    }

    /// Turns `self` into a deterministic transition system whose state colors are pairs of the
    /// original state index and the original color.
    fn into_dts_preserving(
        self,
    ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
        self.collect_dts_preserving()
    }

    /// Turns `self` into a [`MooreMachine`] with the initial state of `self`. Edge colors are dropped.
    fn into_moore(self) -> MooreMachine<Self::Alphabet, StateColor<Self>>
    where
        Self: Pointed,
    {
        let initial = self.initial();
        self.into_moore_with_initial(initial)
    }

    /// Turns `self` into a [`MooreMachine`] with the given initial state. Edge colors are dropped.
    fn into_moore_with_initial(
        self,
        state: StateIndex<Self>,
    ) -> MooreMachine<Self::Alphabet, StateColor<Self>> {
        let (ts, initial) = self.with_initial(state).into_dts_and_initial();
        assert!(ts.size() > 0);
        MooreMachine::from_parts(ts.linked_map_edges(|_, e, _, _| (e, Void)), initial)
    }
    /// Turns `self` into a [`MealyMachine`] with state `0` as initial state. State colors are dropped.
    ///
    /// # Panics
    ///
    /// Panics if `self` has no states.
    fn into_mealy(self) -> MealyMachine<Self::Alphabet, Void, EdgeColor<Self>> {
        let ts = self.into_dts().linked_map_states(|_, _| Void);
        assert!(ts.size() > 0);
        MealyMachine::from_parts(ts, 0)
    }

    /// Collects the transition system representing `self` and builds a new [`DFA`].
    fn into_dfa_with_initial(self, initial: StateIndex<Self>) -> DFA<Self::Alphabet>
    where
        Self: Deterministic<StateColor = bool>,
    {
        let (dts, initial) = self
            .with_initial(initial)
            .erase_edge_colors()
            .into_dts_and_initial();
        DFA::from_parts(dts, initial)
    }

    /// Collects the transition system representing `self` and builds a new [`DFA`], with the initial
    /// state of `self`.
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
    use crate::alphabet::Alphabet;
    use crate::automaton::Automaton;
    use crate::ts::operations::MapStateColor;
    use crate::ts::{EdgeColor, EdgeExpression, StateColor, StateIndex, SymbolOf, operations};
    use crate::{DTS, TransitionSystem};

    impl<A: Alphabet, Q: Color, C: Color> IntoTs for DTS<A, Q, C> {
        // fn into_dts_preserving(
        //     self,
        // ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), C> {
        //     self.zip_state_indices()
        // }
        // fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, C> {
        //     self
        // }
    }
    impl<T: IntoTs, C: Color, F> IntoTs for operations::MapEdgeColor<T, F>
    where
        F: Fn(EdgeColor<T>) -> C,
    {
        // fn into_dts_preserving(self) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<T>), C> {
        //     let (ts, f) = self.into_parts();
        //     ts.into_dts_preserving()
        //         .linked_map_edges(|_, e, c, _| (e, f(c)))
        // }
        // fn into_dts(self) -> DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>> {
        //     let (ts, f) = self.into_parts();
        //     ts.into_dts().linked_map_edges(|_, e, c, _| (e, f(c)))
        // }
    }
    impl<T: IntoTs, Q: Color, F> IntoTs for MapStateColor<T, F>
    where
        T: TransitionSystem,
        F: Fn(T::StateColor) -> Q,
    {
        // fn into_dts(self) -> DTS<Self::Alphabet, Q, EdgeColor<Self>> {
        //     let (ts, f) = self.into_parts();
        //     ts.into_dts().linked_map_states(|_, c| f(c))
        // }
        // fn into_dts_preserving(
        //     self,
        // ) -> DTS<Self::Alphabet, (StateIndex<Self>, StateColor<Self>), EdgeColor<Self>> {
        //     let (ts, f) = self.into_parts();
        //     ts.into_dts_preserving()
        //         .linked_map_states(|_, (i, c)| (i, f(c)))
        // }
    }
    impl<T: IntoTs, F> IntoTs for operations::RestrictByStateIndex<T, F> where
        F: operations::StateIndexFilter<T::StateIndex>
    {
    }
    impl<Ts: IntoTs, P: operations::ProvidesStateColor<Ts::StateIndex>> IntoTs
        for operations::WithStateColor<Ts, P>
    {
    }
    impl<T, D, F> IntoTs for operations::MapEdges<T, F>
    where
        T: IntoTs,
        D: Color,
        F: Fn(StateIndex<T>, &EdgeExpression<T>, EdgeColor<T>, StateIndex<T>) -> D,
    {
    }

    impl<L, R> IntoTs for operations::MatchingProduct<L, R>
    where
        L: IntoTs,
        R: IntoTs,
        R::Alphabet: Alphabet<Symbol = SymbolOf<L>, Expression = EdgeExpression<L>>,
        L::StateColor: Clone,
        R::StateColor: Clone,
    {
    }
    impl<Z, D, const OMEGA: bool> IntoTs
        for Automaton<D::Alphabet, Z, StateColor<D>, EdgeColor<D>, D, OMEGA>
    where
        D: IntoTs,
    {
    }
}

#[cfg(test)]
mod tests {
    use crate::representation::IntoTs;
    use crate::ts::Builder;
    use crate::{Pointed, TransitionSystem};

    #[test]
    fn representation() {
        let ts = Builder::default()
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
