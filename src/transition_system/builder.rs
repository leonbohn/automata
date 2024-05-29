use std::hash::Hash;

use itertools::Itertools;

use crate::prelude::*;

use self::math::Set;

use super::{impls::linked::LinkedListTransitionSystem, IntoEdgeTuple};

/// Helper struct for the construction of non-deterministic transition systems. It stores a list of edges, a list of colors and a default color.
/// This can also be used to construct deterministic transition systems, deterministic parity automata and Mealy machines.
///
/// # Example
///
/// We want to create a DFA with two states 0 and 1 over the alphabet `['a', 'b']`. We want to add the following transitions:
/// - From state 0 to state 0 on symbol 'a'
/// - From state 0 to state 1 on symbol 'b'
/// - From state 1 to state 1 on symbol 'a'
/// - From state 1 to state 0 on symbol 'b'
/// Further, state 0 should be initial and colored `true` and state 1 should be colored `false`. This can be done as follows
/// ```
/// use automata::prelude::*;
///
/// let ts = TSBuilder::default()
///     .with_state_colors([true, false]) // colors given in the order of the states
///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 0)])
///     .into_dfa(0); // 0 is the initial state
/// ```
pub struct TSBuilder<Q = Void, C = Void, const DET: bool = true> {
    symbols: Set<char>,
    edges: Vec<(DefaultIdType, char, C, DefaultIdType)>,
    default: Option<Q>,
    colors: Vec<(DefaultIdType, Q)>,
}

impl<C, const DET: bool> TSBuilder<Void, C, DET> {
    /// Creates an empty instance of `Self`, where states are uncolored (have color [`Void`])
    pub fn without_state_colors() -> Self {
        TSBuilder {
            symbols: Set::default(),
            edges: vec![],
            default: Some(Void),
            colors: vec![],
        }
    }
}
impl<Q, const DET: bool> TSBuilder<Q, Void, DET> {
    /// Creates an empty instance of `Self`, where edges are uncolored (have color [`Void`])
    pub fn without_edge_colors() -> Self {
        TSBuilder {
            symbols: Set::default(),
            edges: vec![],
            default: None,
            colors: vec![],
        }
    }
}

impl<const DET: bool> TSBuilder<Void, Void, DET> {
    /// Creates an empty instance of `Self`, where neither states nor edges have a color (i.e. both
    /// are colored [`Void`]).
    pub fn without_colors() -> Self {
        Self {
            symbols: Set::default(),
            edges: vec![],
            default: Some(Void),
            colors: vec![],
        }
    }
}

impl<Q, C, const DET: bool> Default for TSBuilder<Q, C, DET> {
    fn default() -> Self {
        Self {
            symbols: Set::default(),
            edges: vec![],
            default: None,
            colors: vec![],
        }
    }
}

impl<Q: Color, C: Color, const DET: bool> TSBuilder<Q, C, DET> {
    /// Sets the default color for states that have no color specified.
    pub fn default_color(mut self, color: Q) -> Self {
        self.default = Some(color);
        self
    }

    /// By default, the only alphabet symbols in the transition system that is built
    /// upon creating a concrete transition system are the ones that
    /// appear on at least one transition/edge. This method can be used to force
    /// additional alphabet symbols to appear.
    pub fn with_alphabet_symbols<I>(mut self, symbols: I) -> Self
    where
        I: IntoIterator<Item = char>,
    {
        self.symbols.extend(symbols);
        self
    }

    /// Adds a list of colors to `self`. The colors are assigned to the states in the order in which they are given.
    /// This means if we give the colors `[true, false]` and then add a transition from state `0` to state `1`, then state
    /// `0` will have color `true` and state `1` will have color `false`.
    pub fn with_state_colors<I: IntoIterator<Item = Q>>(self, iter: I) -> Self {
        iter.into_iter()
            .enumerate()
            .fold(self, |acc, (i, x)| acc.color(i as DefaultIdType, x))
    }

    /// Creates an instance of a non-deterministic transition edge lists backed system from `self`.
    pub fn into_edge_lists_nondeterministic(self) -> EdgeListsNondeterministic<CharAlphabet, Q, C>
    where
        C: Hash + Eq,
    {
        let alphabet =
            CharAlphabet::from_iter(self.edges.iter().map(|(_, c, _, _)| *c).chain(self.symbols));

        let num_states = self
            .edges
            .iter()
            .flat_map(|(q, _, _, p)| [*p, *q])
            .unique()
            .count();
        let mut ts = EdgeListsNondeterministic::for_alphabet_size_hint(alphabet, num_states);

        let mut created_states_number = 0;
        for i in 0..num_states {
            let i = DefaultIdType::from_usize(i);
            if self.colors.iter().all(|(q, _)| *q != i) && self.default.is_none() {
                panic!(
                    "Default is needed as some states (specifically {}) have no color",
                    i.show()
                );
            }

            ts.add_state(
                self.colors
                    .iter()
                    .find_map(|(q, c)| if *q == i { Some(c.clone()) } else { None })
                    .unwrap_or_else(|| self.default.clone().unwrap()),
            );
            created_states_number += 1;
        }
        assert_eq!(created_states_number, num_states);

        for (q, e, c, p) in self.edges {
            ts.add_edge((q, e, c, p));
        }
        ts
    }

    /// Creates an instance of a non-deterministic [`GraphTs`] from `self`.
    pub fn into_graphts_nondeterministic(self) -> GraphTs<CharAlphabet, Q, C, false> {
        let alphabet =
            CharAlphabet::from_iter(self.edges.iter().map(|(_, c, _, _)| *c).chain(self.symbols));

        let num_states = self
            .edges
            .iter()
            .flat_map(|(q, _, _, p)| [*p, *q])
            .unique()
            .count();
        let mut ts = GraphTs::for_alphabet_size_hint(alphabet, num_states);

        let mut created_states_number = 0;
        for i in 0..num_states {
            let i = DefaultIdType::from_usize(i);
            if self.colors.iter().all(|(q, _)| *q != i) && self.default.is_none() {
                panic!(
                    "Default is needed as some states (specifically {}) have no color",
                    i.show()
                );
            }

            ts.add_state(
                self.colors
                    .iter()
                    .find_map(|(q, c)| if *q == i { Some(c.clone()) } else { None })
                    .unwrap_or_else(|| self.default.clone().unwrap()),
            );
            created_states_number += 1;
        }
        assert_eq!(created_states_number, num_states);

        for (q, e, c, p) in self.edges {
            ts.add_edge((q, e, c, p));
        }
        ts
    }

    /// Assigns the given `color` to the state with the given index `idx`.
    pub fn color(mut self, idx: DefaultIdType, color: Q) -> Self {
        assert!(self.colors.iter().all(|(q, _c)| q != &idx));
        self.colors.push((idx, color));
        self
    }

    /// Adds a list of transitions to `self`. The transitions are added in the order in which they are given.
    /// The transitions can be passed in as anything that is iterable. An easy way is to pass in an array of tuples.
    ///
    /// # Example
    ///
    /// We want to create a DFA with two states 0 and 1 over the alphabet `['a', 'b']`. We want to add the following transitions:
    /// - From state 0 to state 0 on symbol 'a'
    /// - From state 0 to state 1 on symbol 'b'
    /// - From state 1 to state 1 on symbol 'a'
    /// - From state 1 to state 0 on symbol 'b'
    /// Further, state 0 should be initial and colored `true` and state 1 should be colored `false`. This can be done as follows
    /// ```
    /// use automata::prelude::*;
    ///
    /// let ts = TSBuilder::default()
    ///     .with_state_colors([true, false]) // colors given in the order of the states
    ///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 0)])
    ///     .into_dfa(0); // 0 is the initial state
    /// ```
    pub fn with_transitions<
        E: IntoEdgeTuple<DTS<CharAlphabet, Q, C>>,
        T: IntoIterator<Item = E>,
    >(
        mut self,
        iter: T,
    ) -> Self {
        self.edges
            .extend(iter.into_iter().map(|t| t.into_edge_tuple()));
        self
    }

    /// Adds a list of edges to `self`. The edges are added in the order in which they are given.
    /// The edges can be passed in as anything that is iterable. An easy way is to pass in an array of tuples.
    /// Note, that in comparison to [`Self::with_transitions`], this method adds **edges** and so the individual
    /// elements that are added must store/provide [`Expression`]s instead of [`Symbol`]s.
    ///
    /// This method accepts any iterable yielding objects that implement [`IntoEdgeTuple`] for the stored color `C`.
    /// If the desired edge color is [`Void`], then we may simply omit it from the tuples. The only restriction
    /// on this is that either all or none of the yielded tuples have a color.
    ///
    /// # Example
    ///
    /// We want to create a DFA with two states 0 and 1 over the alphabet `['a', 'b']`. We want to add the following transitions:
    /// - From state 0 to state 0 on symbol 'a'
    /// - From state 0 to state 1 on symbol 'b'
    /// - From state 1 to state 1 on symbol 'a'
    /// - From state 1 to state 0 on symbol 'b'
    /// Further, state 0 should be initial and colored `true` and state 1 should be colored `false`. This can be done as follows
    /// ```
    /// use automata::prelude::*;
    ///
    /// let ts = TSBuilder::default()
    ///     .with_state_colors([true, false]) // colors given in the order of the states
    ///     .with_edges([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1)])
    ///     .with_edges([(1, 'b', 0)]) // We can also skip the `Void` entry at position 3
    ///     .into_dfa(0); // 0 is the initial state
    /// ```
    pub fn with_edges<E: IntoEdgeTuple<DTS<CharAlphabet, Q, C>>, I: IntoIterator<Item = E>>(
        mut self,
        iter: I,
    ) -> Self {
        self.edges
            .extend(iter.into_iter().map(|e| e.into_edge_tuple()));
        self
    }

    /// Collects self into a non-deterministic transition system.
    pub fn into_linked_list_nondeterministic(
        self,
    ) -> LinkedListNondeterministic<CharAlphabet, Q, C> {
        let alphabet =
            CharAlphabet::from_iter(self.edges.iter().map(|(_, c, _, _)| *c).chain(self.symbols));
        let num_states = self
            .edges
            .iter()
            .flat_map(|(q, _, _, p)| [*p, *q])
            .unique()
            .count();
        let mut ts = LinkedListNondeterministic::for_alphabet_size_hint(alphabet, num_states);
        let colors_it = (0..num_states).map(|x| {
            if let Some(color) = self.colors.iter().find_map(|(q, c)| {
                if (*q as usize) == x {
                    Some(c.clone())
                } else {
                    None
                }
            }) {
                color
            } else {
                self.default.clone().unwrap_or_else(|| {
                    panic!(
                        "Default is needed as some states (specifically {}) have no color",
                        x.show()
                    )
                })
            }
        });
        let created_states_number = ts.extend_states(colors_it).count();
        assert_eq!(created_states_number, num_states);

        for (q, e, c, p) in self.edges {
            ts.add_edge((q as usize, e, c, p as usize));
        }
        ts
    }
}

impl<Q: Color, C: Color> TSBuilder<Q, C, true> {
    /// Builds an instance of [`DTS`] from `self`.
    #[cfg(not(feature = "linked_list_ts"))]
    pub fn into_dts(self) -> DTS<CharAlphabet, Q, C> {
        let alphabet =
            CharAlphabet::from_iter(self.edges.iter().map(|(_, c, _, _)| *c).chain(self.symbols));

        let num_states = self
            .edges
            .iter()
            .flat_map(|(q, _, _, p)| [*p, *q])
            .unique()
            .count();
        let mut ts = DTS::for_alphabet_size_hint(alphabet, num_states);

        let mut created_states_number = 0;
        for i in 0..num_states {
            let i = DefaultIdType::from_usize(i);
            if self.colors.iter().all(|(q, _)| *q != i) && self.default.is_none() {
                panic!(
                    "Default is needed as some states (specifically {}) have no color",
                    i.show()
                );
            }

            ts.add_state(
                self.colors
                    .iter()
                    .find_map(|(q, c)| if *q == i { Some(c.clone()) } else { None })
                    .unwrap_or_else(|| self.default.clone().unwrap()),
            );
            created_states_number += 1;
        }
        assert_eq!(created_states_number, num_states);

        for (q, e, c, p) in self.edges {
            ts.add_edge((q, e, c, p));
        }
        ts
    }
    /// Builds an instance of [`DTS`] from `self` and sets the given `initial` state
    /// as the designated initial state of the output object.
    pub fn into_dts_with_initial(
        self,
        initial: DefaultIdType,
    ) -> WithInitial<DTS<CharAlphabet, Q, C>>
    where
        C: Hash + Eq,
    {
        self.into_dts().with_initial(initial)
    }

    /// Build a deterministic transition system from `self`. Panics if `self` is not deterministic.
    pub fn into_linked_list_deterministic(self) -> LinkedListTransitionSystem<CharAlphabet, Q, C> {
        self.into_linked_list_nondeterministic()
            .into_deterministic()
    }
    /// Creates an instance of a deterministic transition edge lists backed system from `self`.
    pub fn into_edge_lists_deterministic(self) -> EdgeLists<CharAlphabet, Q, C>
    where
        C: Hash + Eq,
    {
        self.into_edge_lists_nondeterministic().into_deterministic()
    }
    /// Turns `self` into a [`RightCongruence`] with the given initial state. Panics if `self` is not deterministic.
    pub fn into_right_congruence(
        self,
        initial: DefaultIdType,
    ) -> RightCongruence<CharAlphabet, Q, C> {
        self.into_dts()
            .with_initial(initial)
            .collect_right_congruence()
    }
    /// Build a deterministic transition system from `self` and set the given `initial` state as the
    /// designated initial state of the output object. Panics if `self` is not deterministic.
    pub fn into_linked_list_deterministic_with_initial(
        self,
        initial: usize,
    ) -> WithInitial<LinkedListTransitionSystem<CharAlphabet, Q, C>> {
        self.into_linked_list_deterministic().with_initial(initial)
    }
    /// Creates an instance of a deterministic transition edge lists backed system from `self`.
    pub fn into_edge_lists_deterministic_with_initial(
        self,
        initial: DefaultIdType,
    ) -> WithInitial<EdgeListsDeterministic<CharAlphabet, Q, C>>
    where
        C: Hash + Eq,
    {
        self.into_edge_lists_deterministic().with_initial(initial)
    }
}

impl TSBuilder<bool, Void, true> {
    /// Tries to turn `self` into a deterministic finite automaton. Panics if `self` is not deterministic.
    pub fn into_dfa(self, initial: DefaultIdType) -> DFA<CharAlphabet> {
        self.into_dts().with_initial(initial).collect_dfa()
    }
}

impl TSBuilder<Void, bool, true> {
    /// Attempts to turn `self` into a deterministic Büchi automaton. Panics if `self` is not deterministic.
    pub fn into_dba(self, initial: DefaultIdType) -> DBA<CharAlphabet> {
        self.default_color(Void)
            .into_dts()
            .with_initial(initial)
            .collect_dba()
    }
}

impl TSBuilder<Void, Int, true> {
    /// Attempts to turn `self` into a deterministic parity automaton. Panics if `self` is not deterministic.
    pub fn into_dpa(self, initial: DefaultIdType) -> DPA<CharAlphabet> {
        self.default_color(Void)
            .into_dts()
            .with_initial(initial)
            .collect_dpa()
    }

    /// Builds a Mealy machine from `self`. Panics if `self` is not deterministic.
    pub fn into_mealy(self, initial: DefaultIdType) -> MealyMachine<CharAlphabet> {
        self.default_color(Void)
            .into_dts()
            .with_initial(initial)
            .collect_mealy()
    }
}

impl TSBuilder<Int, Void, true> {
    /// Builds a Moore machine from `self`. Panics if `self` is not deterministic.
    pub fn into_moore(self, initial: DefaultIdType) -> MooreMachine<CharAlphabet> {
        self.into_dts().with_initial(initial).collect_moore()
    }
}

impl<Q: Color, C: Color> TSBuilder<Q, C, true> {
    /// Turns `self` into a [`RightCongruence`] with the given initial state while also erasing all state and edge
    /// colors. Panics if `self` is not deterministic.
    pub fn into_right_congruence_bare(
        self,
        initial: DefaultIdType,
    ) -> RightCongruence<CharAlphabet> {
        self.into_dts()
            .with_initial(initial)
            .erase_state_colors()
            .erase_edge_colors()
            .collect_right_congruence()
    }
}
