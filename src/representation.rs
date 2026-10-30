use crate::ts::{
    CompactIdMap, DenseId, EdgeExpression, EdgeRef, IdType, StateMap, States,
};
use crate::{Color, Int, Void};
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::automaton::{DBA, DFA, DPA, MealyMachine, MooreMachine};
use crate::ts::{
    DefaultIdType, Deterministic, EdgeColor, ForAlphabet, Sproutable, StateColor, StateIndex,
};
use crate::{Congruence, DTS, Pointed, RightCongruence, TransitionSystem};

/// Marker trait for transition systems whose states are colored with `Q`.
pub trait StateColored<Q: Color = Int> {}
impl<T: TransitionSystem> StateColored<StateColor<T>> for T {}

/// Marker trait for transition systems whose edges are colored with `C`.
pub trait EdgeColored<C: Color = Int> {}
impl<T: TransitionSystem> EdgeColored<EdgeColor<T>> for T {}

/// The pieces of a transition system, as handed from an [`IntoTransitions`] source to a
/// [`FromTransitions`] target. Just like the pieces of an iterator pipeline they are consumed in
/// a single pass: all `states` first, then all `edges`.
///
/// `Init` is `()` for a system without a designated initial state and the index of that state
/// for a pointed system or an automaton.
#[derive(Clone, Debug)]
pub struct Parts<A, S, E, Init = ()> {
    /// The alphabet of the system.
    pub alphabet: A,
    /// The states with their colors. Every state occurs exactly once.
    pub states: S,
    /// The edges `(source, expression, color, target)`; their endpoints occur in `states`.
    pub edges: E,
    /// The initial state, if there is one.
    pub initial: Init,
}

/// The owned counterpart of the edges of a system with the given index type, the item type of
/// [`IntoTransitions::IntoEdges`].
pub type OwnedEdge<Ts> = (
    <Ts as TransitionSystem>::StateIndex,
    EdgeExpression<Ts>,
    <Ts as TransitionSystem>::EdgeColor,
    <Ts as TransitionSystem>::StateIndex,
);

/// Takes a transition system apart into its [`Parts`], like [`IntoIterator`] does for collections.
/// This is the source side of [`IntoTransitions::collect`].
///
/// Systems that own their data (storages and the adapters on top of them) hand out their states
/// and edges without cloning. A reference `&T` to any [`States`] system yields clones, which is
/// what [`IntoIterator`] for `&Vec<T>` does for a vector. Adapters like
/// [`Recolor`](crate::ts::operations::Recolor) wrap the iterators of the system they adapt, so
/// that `ts.map_edge_colors(f).erase_state_colors().collect::<DTS<..>>()` is a single pass.
///
/// A system that is [`Pointed`] or an [`Automaton`](crate::automaton::Automaton) also hands out
/// its initial state ([`Self::Initial`]); plain systems do not and have to be given one with
/// [`TransitionSystem::with_initial`] before they can be collected into an automaton.
pub trait IntoTransitions: TransitionSystem {
    /// `()` for systems without initial state, the index of the initial state otherwise.
    type Initial;
    /// The states with their colors, each exactly once.
    type IntoStates: Iterator<Item = (Self::StateIndex, Self::StateColor)>;
    /// All edges as `(source, expression, color, target)`.
    type IntoEdges: Iterator<Item = OwnedEdge<Self>>;

    /// Takes `self` apart.
    fn into_transitions(
        self,
    ) -> Parts<Self::Alphabet, Self::IntoStates, Self::IntoEdges, Self::Initial>;

    /// Builds a `T` from the states and edges of `self`, like [`Iterator::collect`]. The states
    /// of the result are numbered `0, 1, ...` in the order in which `self` yields them, so the
    /// indices may change, see [`Self::collect_with_map`] to learn how.
    ///
    /// # Panics
    /// Panics if `self` is pointed and its initial state is not one of its states.
    ///
    /// # Example
    /// ```
    /// use automata::{DTS, Void, ts::{Builder, States, TransitionSystem}, representation::IntoTransitions};
    ///
    /// let ts = Builder::without_colors()
    ///     .with_edges([(2, 'a', 5), (5, 'a', 2)])
    ///     .into_dts();
    /// let collected: DTS = ts.map_state_colors(|_| Void).collect();
    /// assert_eq!(collected.state_count(), 2);
    /// ```
    fn collect<T>(self) -> T
    where
        Self: Sized,
        T: FromTransitions<
                Self::StateIndex,
                Self::Initial,
                Alphabet = Self::Alphabet,
                StateColor = Self::StateColor,
                EdgeColor = Self::EdgeColor,
            >,
    {
        T::from_transitions(self.into_transitions())
    }

    /// Like [`Self::collect`], but also returns the numbering that was applied to the states.
    fn collect_with_map<T>(self) -> (T, CompactIdMap<Self::StateIndex>)
    where
        Self: Sized,
        T: FromTransitions<
                Self::StateIndex,
                Self::Initial,
                Alphabet = Self::Alphabet,
                StateColor = Self::StateColor,
                EdgeColor = Self::EdgeColor,
            >,
    {
        let Parts {
            alphabet,
            states,
            edges,
            initial,
        } = self.into_transitions();
        let mut order = Vec::new();
        let target = T::from_transitions(Parts {
            alphabet,
            states: states.inspect(|(q, _)| order.push(*q)),
            edges,
            initial,
        });
        (target, CompactIdMap::from_states(order))
    }
}

/// Builds a transition system from [`Parts`], like [`FromIterator`] builds a collection. This is
/// the target side of [`IntoTransitions::collect`]. `I` is the type of the state indices of the
/// source and `Init` the type of its initial state, see [`Parts`].
///
/// # Contract
/// The `n`-th state of `parts.states` becomes state `n` of the result. Edges are added in the
/// order they arrive. Storages ignore the initial state, automata use it.
pub trait FromTransitions<I: IdType, Init = ()>: TransitionSystem + Sized {
    /// Builds `Self` from `parts`.
    ///
    /// # Panics
    /// Panics if an edge touches a state that is not in `parts.states`.
    fn from_transitions<S, E>(parts: Parts<Self::Alphabet, S, E, Init>) -> Self
    where
        S: Iterator<Item = (I, Self::StateColor)>,
        E: Iterator<Item = (I, EdgeExpression<Self>, Self::EdgeColor, I)>;
}

/// Hands out the numbers `0, 1, ...` for the ids of a stream of states, in order of arrival. As
/// long as the ids are already `0, 1, ...` nothing is stored.
pub(crate) struct Renumbering<I> {
    count: u32,
    map: Option<StateMap<I, u32>>,
}

impl<I: IdType> Renumbering<I> {
    pub(crate) fn new() -> Self {
        Self {
            count: 0,
            map: None,
        }
    }

    /// Registers the next state and returns its number.
    #[inline]
    pub(crate) fn push(&mut self, id: I) -> u32 {
        let number = self.count;
        self.count += 1;
        match &mut self.map {
            None if id.to_dense() == Some(number as usize) => {}
            None => {
                let mut map = StateMap::new(Some(0));
                for earlier in 0..number {
                    let earlier_id = I::from_dense(earlier as usize)
                        .expect("ids that arrived in order are dense");
                    map.insert(earlier_id, earlier);
                }
                map.insert(id, number);
                self.map = Some(map);
            }
            Some(map) => {
                map.insert(id, number);
            }
        }
        number
    }

    /// The number of a state that was registered before.
    ///
    /// # Panics
    /// Panics if `id` was not registered.
    #[inline]
    pub(crate) fn get(&self, id: I) -> u32 {
        match &self.map {
            None => match id.to_dense() {
                Some(n) if n < self.count as usize => n as u32,
                _ => panic!("edge touches the state {id:?}, which is not among the states"),
            },
            Some(map) => *map
                .get(&id)
                .unwrap_or_else(|| panic!("edge touches the state {id:?}, which is not among the states")),
        }
    }
}

/// Builds a growable system from parts, see [`FromTransitions`].
pub(crate) fn sprout_from_parts<T, I, S, E, Init>(parts: Parts<T::Alphabet, S, E, Init>) -> T
where
    T: Sproutable + ForAlphabet<T::Alphabet>,
    T::StateIndex: DenseId,
    I: IdType,
    S: Iterator<Item = (I, T::StateColor)>,
    E: Iterator<Item = (I, EdgeExpression<T>, T::EdgeColor, I)>,
{
    let Parts {
        alphabet,
        states,
        edges,
        ..
    } = parts;
    let mut out = T::for_alphabet_size_hint(alphabet, states.size_hint().0);
    let mut numbering = Renumbering::new();
    for (q, color) in states {
        numbering.push(q);
        out.add_state(color);
    }
    for (p, expression, color, r) in edges {
        out.add_edge((
            T::StateIndex::from_usize(numbering.get(p) as usize),
            expression,
            color,
            T::StateIndex::from_usize(numbering.get(r) as usize),
        ));
    }
    out
}

/// Iterator over the states of a borrowed system with their colors cloned, see
/// [`IntoTransitions`] for `&T`.
pub struct RefStates<'a, T: States + 'a> {
    ts: &'a T,
    states: T::StatesIter<'a>,
}

impl<'a, T: States> Iterator for RefStates<'a, T> {
    type Item = (T::StateIndex, T::StateColor);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let q = self.states.next()?;
        let color = self.ts.state_color(q).expect("a state of the system has a color");
        Some((q, color.into_owned()))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.states.size_hint()
    }
}

/// Iterator over the edges of a borrowed system, cloned, see [`IntoTransitions`] for `&T`.
pub struct RefEdges<'a, T: States + 'a> {
    ts: &'a T,
    states: T::StatesIter<'a>,
    current: Option<T::EdgesFromIter<'a>>,
}

impl<'a, T: States> Iterator for RefEdges<'a, T> {
    type Item = OwnedEdge<T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(edges) = &mut self.current
                && let Some(edge) = edges.next()
            {
                return Some(edge.into_tuple());
            }
            let q = self.states.next()?;
            self.current = self.ts.edges_from(q);
        }
    }
}

/// A reference yields clones of the states and edges, like `&Vec<T>` yields clones in a
/// [`FromIterator`] chain after `.cloned()`. The result has no initial state; to keep one of a
/// [`Pointed`] system `p`, use `(&p).with_initial(p.initial())`.
impl<'a, T: States> IntoTransitions for &'a T {
    type Initial = ();
    type IntoStates = RefStates<'a, T>;
    type IntoEdges = RefEdges<'a, T>;

    fn into_transitions(self) -> Parts<T::Alphabet, Self::IntoStates, Self::IntoEdges, ()> {
        Parts {
            alphabet: self.alphabet().clone(),
            states: RefStates {
                ts: self,
                states: self.states(),
            },
            edges: RefEdges {
                ts: self,
                states: self.states(),
                current: None,
            },
            initial: (),
        }
    }
}

/// The states and edges of a system, collected into vectors. Used by systems that cannot hand out
/// their pieces without first computing them.
pub(crate) fn materialize<T: TransitionSystem>(
    ts: &T,
    states: impl IntoIterator<Item = T::StateIndex>,
) -> (
    std::vec::IntoIter<(T::StateIndex, T::StateColor)>,
    std::vec::IntoIter<OwnedEdge<T>>,
) {
    let mut colored = Vec::new();
    let mut edges = Vec::new();
    for q in states {
        colored.push((
            q,
            ts.state_color(q)
                .expect("a state of the system has a color")
                .into_owned(),
        ));
        edges.extend(
            ts.edges_from(q)
                .expect("a state of the system has edges")
                .map(EdgeRef::into_tuple),
        );
    }
    (colored.into_iter(), edges.into_iter())
}

/// Collects (a reference to) any transition system into a concrete data structure or automaton,
/// which evaluates all lazy operations that are applied to it. The states of the result are
/// numbered `0, 1, ...` in the order of the original indices, so the indices may change.
///
/// The methods with a `_preserving` suffix keep the original index of each state as the first
/// component of its color. Methods that need an initial state are only available for
/// [`Pointed`] transition systems.
#[allow(clippy::type_complexity)]
pub trait CollectTs: States {
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
            .states_with_color()
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
        let mut out = DTS::for_alphabet_size_hint(self.alphabet().clone(), self.state_count());
        let mut map = BTreeMap::default();

        for (q, c) in self.states_with_color() {
            map.insert(q, out.add_state((q, c)));
        }
        for q in self.states() {
            for e in self.edges_from(q).unwrap() {
                out.add_edge((
                    *map.get(&e.source()).unwrap(),
                    e.expression().clone(),
                    e.color().clone(),
                    *map.get(&e.target()).unwrap(),
                ));
            }
        }

        debug_assert_eq!(self.state_count(), out.state_count());
        #[cfg(debug_assertions)]
        out.check_consistency();

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
    fn collect_dfa(&self) -> DFA<DTS<Self::Alphabet, bool, Void>>
    where
        Self: Pointed<StateColor = bool>,
    {
        let (ts, initial) = self.erase_edge_colors().collect_dts_and_initial();
        DFA::from_parts(ts, initial)
    }

    /// Collects into a [`MooreMachine`], with the initial state of `self`. Edge colors are dropped.
    fn collect_moore(&self) -> MooreMachine<DTS<Self::Alphabet, StateColor<Self>, Void>>
    where
        Self: Pointed,
    {
        let (ts, initial) = self.erase_edge_colors().collect_dts_and_initial();
        MooreMachine::from_parts(ts, initial)
    }
    /// Collects into a [`MealyMachine`], with the initial state of `self`.
    fn collect_mealy(&self) -> MealyMachine<DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>>
    where
        Self: Pointed,
    {
        let (ts, initial) = self.collect_dts_and_initial();
        MealyMachine::from_parts(ts, initial)
    }
    /// Collects into a [`DBA`], with the initial state of `self`. State colors are dropped.
    fn collect_dba(&self) -> DBA<DTS<Self::Alphabet, Void, bool>>
    where
        Self: Pointed<EdgeColor = bool>,
    {
        let (ts, initial) = self.erase_state_colors().collect_dts_and_initial();
        DBA::from_parts(ts, initial)
    }
    /// Collects into a [`DPA`], with the initial state of `self`. State colors are dropped.
    fn collect_dpa(&self) -> DPA<DTS<Self::Alphabet, Void, Int>>
    where
        Self: Pointed<EdgeColor = Int>,
    {
        let (ts, initial) = self.erase_state_colors().collect_dts_and_initial();
        DPA::from_parts(ts, initial)
    }
    /// Collects into a [`RightCongruence`], with the initial state of `self`.
    fn collect_right_congruence(
        &self,
    ) -> RightCongruence<DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>>
    where
        Self: Pointed,
    {
        let (ts, initial) = self.collect_dts_and_initial();
        RightCongruence::from_parts(ts, initial)
    }
}
impl<Ts: States> CollectTs for Ts {}

/// Like [`CollectTs`], but consumes the transition system.
#[allow(clippy::type_complexity)]
pub trait IntoTs: States {
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
            .states_with_color()
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
    fn into_moore(self) -> MooreMachine<DTS<Self::Alphabet, StateColor<Self>, Void>>
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
    ) -> MooreMachine<DTS<Self::Alphabet, StateColor<Self>, Void>> {
        let (ts, initial) = self.with_initial(state).into_dts_and_initial();
        assert!(ts.state_count() > 0);
        MooreMachine::from_parts(ts.linked_map_edge_colors(|_, _, _, _| Void), initial)
    }
    /// Turns `self` into a [`MealyMachine`] with state `0` as initial state. State colors are dropped.
    ///
    /// # Panics
    ///
    /// Panics if `self` has no states.
    fn into_mealy(self) -> MealyMachine<DTS<Self::Alphabet, Void, EdgeColor<Self>>> {
        let ts = self.into_dts().linked_map_states(|_, _| Void);
        assert!(ts.state_count() > 0);
        MealyMachine::from_parts(ts, 0)
    }

    /// Collects the transition system representing `self` and builds a new [`DFA`].
    fn into_dfa_with_initial(
        self,
        initial: StateIndex<Self>,
    ) -> DFA<DTS<Self::Alphabet, bool, Void>>
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
    fn into_dfa(self) -> DFA<DTS<Self::Alphabet, bool, Void>>
    where
        Self: Pointed + Congruence<StateColor = bool>,
    {
        let initial = self.initial();
        self.into_dfa_with_initial(initial)
    }

    /// Collects the transition system representing `self` and builds a new [`DPA`].
    fn into_dpa_with_initial(self, initial: StateIndex<Self>) -> DPA<DTS<Self::Alphabet, Void, Int>>
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
    fn into_dpa(self) -> DPA<DTS<Self::Alphabet, Void, Int>>
    where
        Self: Congruence<EdgeColor = Int>,
    {
        let initial = self.initial();
        self.into_dpa_with_initial(initial)
    }

    /// Collects the transition system representing `self` and builds a new [`DBA`].
    fn into_dba_with_initial(
        self,
        initial: StateIndex<Self>,
    ) -> DBA<DTS<Self::Alphabet, Void, bool>>
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
    fn into_dba(self) -> DBA<DTS<Self::Alphabet, Void, bool>>
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
    ) -> RightCongruence<DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>>
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
    use crate::ts::operations;
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
    impl<T: IntoTs, FS, FE> IntoTs for operations::Recolor<T, FS, FE>
    where
        FS: operations::StateRecolor<T>,
        FE: operations::EdgeRecolor<T>,
    {
    }
    impl<T: IntoTs, F> IntoTs for operations::RestrictByStateIndex<T, F> where
        F: operations::StateIndexFilter<T::StateIndex>
    {
    }
    impl<Ts: TransitionSystem> IntoTs for operations::ReachablePart<Ts> {}
    impl<Sem, D> IntoTs for Automaton<D, Sem> where D: IntoTs {}
}

#[cfg(test)]
mod tests {
    use crate::Pointed;
    use crate::States;
    use crate::representation::IntoTs;
    use crate::ts::Builder;

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
        assert_eq!(moore.state_count(), mealy.state_count());
        assert_eq!(moore.initial(), mealy.initial());
    }
}

#[cfg(test)]
mod collect_tests {
    use super::{IntoTransitions, Parts};
    use crate::alphabet::CharAlphabet;
    use crate::automaton::{DFA, DPA};
    use crate::ts::{
        Builder, CsrTs, DenseTs, Deterministic, Pointed, Shrinkable, Sproutable, States,
        TransitionSystem,
    };
    use crate::{DTS, Void};

    fn sample() -> DTS<CharAlphabet, bool, u32> {
        Builder::default()
            .with_state_colors([false, true, false])
            .with_edges([
                (0, 'a', 1, 1),
                (0, 'b', 2, 2),
                (1, 'a', 3, 2),
                (1, 'b', 4, 0),
                (2, 'a', 5, 2),
                (2, 'b', 6, 1),
            ])
            .into_dts()
    }

    fn edges<T>(ts: &T) -> Vec<(u32, char, u32, u32)>
    where
        T: States<Alphabet = CharAlphabet, StateIndex = u32, EdgeColor = u32>,
    {
        let mut edges: Vec<_> = ts
            .states()
            .flat_map(|q| ts.edges_from(q).unwrap().collect::<Vec<_>>())
            .map(|e| (e.source(), *e.expression(), *e.color(), e.target()))
            .collect();
        edges.sort();
        edges
    }

    fn same_edges<A, B>(a: &A, b: &B)
    where
        A: States<Alphabet = CharAlphabet, StateIndex = u32, EdgeColor = u32>,
        B: States<Alphabet = CharAlphabet, StateIndex = u32, EdgeColor = u32>,
    {
        assert_eq!(edges(a), edges(b));
    }

    #[test]
    fn owned_and_borrowed_collect_into_every_storage() {
        let ts = sample();
        let by_ref: DTS<CharAlphabet, bool, u32> = (&ts).collect();
        same_edges(&ts, &by_ref);
        let owned: DTS<CharAlphabet, bool, u32> = ts.clone().collect();
        same_edges(&ts, &owned);
        let dense: DenseTs<CharAlphabet, bool, u32> = ts.clone().collect();
        same_edges(&ts, &dense);
        let csr: CsrTs<CharAlphabet, bool, u32> = ts.clone().collect();
        csr.check_consistency();
        same_edges(&ts, &csr);
        let back: DTS<CharAlphabet, bool, u32> = csr.collect();
        same_edges(&ts, &back);
        let back: DTS<CharAlphabet, bool, u32> = dense.collect();
        same_edges(&ts, &back);
    }

    #[test]
    fn collecting_renumbers_after_removals() {
        let mut ts = sample();
        ts.remove_state(1);
        let (collected, map): (DTS<CharAlphabet, bool, u32>, _) = ts.clone().collect_with_map();
        assert_eq!(collected.state_count(), 2);
        assert_eq!(map.states(), &[0, 2]);
        assert_eq!(map.id(&2), Some(1));
        assert_eq!(collected.successor(1, 'a'), Some(1));
        assert_eq!(collected.successor(1, 'b'), None);
        // the borrowed version renumbers in the same way
        let (by_ref, by_ref_map): (DTS<CharAlphabet, bool, u32>, _) = (&ts).collect_with_map();
        same_edges(&collected, &by_ref);
        assert_eq!(by_ref_map.states(), map.states());
    }

    #[test]
    fn adapters_are_a_single_pass() {
        let collected: DTS<CharAlphabet, Void, bool> = sample()
            .erase_state_colors()
            .map_edge_colors(|c| c % 2 == 0)
            .collect();
        assert_eq!(collected.state_count(), 3);
        assert!(!collected.edge(0, 'a').unwrap().color());
        assert!(collected.edge(0, 'b').unwrap().color());
    }

    #[test]
    fn automata_keep_their_initial_state() {
        let mut ts = sample();
        ts.remove_state(0);
        // state 2 becomes state 1
        let dfa: DFA<DTS<CharAlphabet, bool, Void>> =
            ts.clone().erase_edge_colors().with_initial(2).collect();
        assert_eq!(dfa.initial(), 1);
        assert!(!dfa.accepts("a"));
        assert!(dfa.accepts("b"));
        let dpa: DPA<DTS<CharAlphabet, Void, u32>> =
            ts.erase_state_colors().with_initial(1).collect();
        assert_eq!(dpa.initial(), 0);
        // and from an automaton to a plain system
        let back: DTS<CharAlphabet, Void, u32> = dpa.collect();
        assert_eq!(back.state_count(), 2);
    }

    #[test]
    #[should_panic(expected = "initial state")]
    fn missing_initial_state_panics() {
        let _: DFA<DTS<CharAlphabet, bool, Void>> =
            sample().erase_edge_colors().with_initial(7).collect();
    }

    #[test]
    fn parts_can_be_taken_apart() {
        let Parts { states, edges, .. } = sample().into_transitions();
        assert_eq!(states.count(), 3);
        assert_eq!(edges.count(), 6);
    }

    #[test]
    fn reachable_part_collects_only_reachable_states() {
        let mut ts = sample();
        ts.add_state(false);
        let reachable: DTS<CharAlphabet, bool, u32> = ts.with_initial(0).reachable_part().collect();
        assert_eq!(reachable.state_count(), 3);
    }
}
