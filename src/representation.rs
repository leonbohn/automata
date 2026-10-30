use crate::ts::{
    CompactIdMap, DenseId, EdgeColor, EdgeExpression, EdgeRef, ForAlphabet, IdType, Sproutable,
    StateColor, StateMap, States,
};
use crate::{Color, Int, Void};

use crate::automaton::{DBA, DFA, DPA, MealyMachine, MooreMachine};
use crate::{DTS, Pointed, RightCongruence, TransitionSystem};

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
    /// Adapters are applied while collecting, there is no intermediate transition system.
    /// ```
    /// use automata::{DTS, Void, ts::{Builder, States, TransitionSystem}, representation::IntoTransitions};
    ///
    /// let ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 1), (1, 'a', 0)])
    ///     .into_dts();
    /// let collected: DTS<_, Void, bool> = ts.map_edge_colors(|_| true).collect();
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
    ///
    /// # Example
    /// ```
    /// use automata::{DTS, ts::{Builder, Shrinkable, States}, representation::IntoTransitions};
    ///
    /// let mut ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 2), (2, 'a', 0), (1, 'a', 1)])
    ///     .into_dts();
    /// ts.remove_state(1);
    /// let (collected, map) = ts.collect_with_map::<DTS>();
    /// assert_eq!(collected.state_count(), 2);
    /// // the state that had index 2 has index 1 now
    /// assert_eq!(map.id(&2), Some(1));
    /// ```
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
            Some(map) => *map.get(&id).unwrap_or_else(|| {
                panic!("edge touches the state {id:?}, which is not among the states")
            }),
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

/// Builds `T` from the parts of a pointed system and returns it together with the index that its
/// initial state received. Used by the automata, which add the initial state to a plain system.
///
/// # Panics
/// Panics if the initial state is not among the states.
pub(crate) fn pointed_from_parts<T, I, S, E>(
    parts: Parts<T::Alphabet, S, E, I>,
) -> (T, T::StateIndex)
where
    T: FromTransitions<I>,
    T::StateIndex: DenseId,
    I: IdType,
    S: Iterator<Item = (I, T::StateColor)>,
    E: Iterator<Item = (I, EdgeExpression<T>, T::EdgeColor, I)>,
{
    let Parts {
        alphabet,
        states,
        edges,
        initial,
    } = parts;
    let mut new_initial = None;
    let ts = T::from_transitions(Parts {
        alphabet,
        states: states.enumerate().map(|(n, (q, color))| {
            if q == initial {
                new_initial = Some(n);
            }
            (q, color)
        }),
        edges,
        initial: (),
    });
    let initial = new_initial.expect("the initial state is not among the states");
    (ts, T::StateIndex::from_usize(initial))
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
        let color = self
            .ts
            .state_color(q)
            .expect("a state of the system has a color");
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

/// The iterators over the vectors that [`materialize`] returns.
pub(crate) type Materialized<T> = (
    std::vec::IntoIter<(
        <T as TransitionSystem>::StateIndex,
        <T as TransitionSystem>::StateColor,
    )>,
    std::vec::IntoIter<OwnedEdge<T>>,
);

/// The states and edges of a system, collected into vectors. Used by systems that cannot hand out
/// their pieces without first computing them.
pub(crate) fn materialize<T: TransitionSystem>(
    ts: &T,
    states: impl IntoIterator<Item = T::StateIndex>,
) -> Materialized<T> {
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

/// Shorthands that collect a [`Pointed`] transition system (by reference, so `self` is cloned)
/// into the common automata, dropping the colors the automaton does not have. They are a
/// single [`IntoTransitions::collect`] each; for example `ts.collect_dfa()` is
/// `ts.erase_edge_colors().with_initial(ts.initial()).collect()`. To consume `self` instead,
/// use `collect` directly.
pub trait CollectPointed: Pointed + States {
    /// Collects into a [`DFA`], with the initial state of `self`. Edge colors are dropped.
    fn collect_dfa(&self) -> DFA<DTS<Self::Alphabet, bool, Void>>
    where
        Self: Pointed<StateColor = bool>,
    {
        self.erase_edge_colors()
            .with_initial(self.initial())
            .collect()
    }

    /// Collects into a [`MooreMachine`], with the initial state of `self`. Edge colors are dropped.
    fn collect_moore(&self) -> MooreMachine<DTS<Self::Alphabet, StateColor<Self>, Void>> {
        self.erase_edge_colors()
            .with_initial(self.initial())
            .collect()
    }

    /// Collects into a [`MealyMachine`], with the initial state of `self`.
    fn collect_mealy(
        &self,
    ) -> MealyMachine<DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>> {
        self.with_initial(self.initial()).collect()
    }

    /// Collects into a [`DBA`], with the initial state of `self`. State colors are dropped.
    fn collect_dba(&self) -> DBA<DTS<Self::Alphabet, Void, bool>>
    where
        Self: Pointed<EdgeColor = bool>,
    {
        self.erase_state_colors()
            .with_initial(self.initial())
            .collect()
    }

    /// Collects into a [`DPA`], with the initial state of `self`. State colors are dropped.
    fn collect_dpa(&self) -> DPA<DTS<Self::Alphabet, Void, Int>>
    where
        Self: Pointed<EdgeColor = Int>,
    {
        self.erase_state_colors()
            .with_initial(self.initial())
            .collect()
    }

    /// Collects into a [`RightCongruence`], with the initial state of `self`.
    fn collect_right_congruence(
        &self,
    ) -> RightCongruence<DTS<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>> {
        self.with_initial(self.initial()).collect()
    }
}
impl<Ts: Pointed + States> CollectPointed for Ts {}

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
