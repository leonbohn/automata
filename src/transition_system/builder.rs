use itertools::Itertools;

use crate::{prelude::*, Void};

use super::IntoEdge;

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
///     .with_colors([true, false]) // colors given in the order of the states
///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 0)])
///     .into_dfa(0); // 0 is the initial state
/// ```
pub struct TSBuilder<Q = Void, C = Void> {
    edges: Vec<(usize, char, C, usize)>,
    default: Option<Q>,
    colors: Vec<(usize, Q)>,
}

impl<C> TSBuilder<Void, C> {
    /// Creates an empty instance of `Self`, where states are uncolored (have color [`Void`])
    pub fn without_state_colors() -> Self {
        TSBuilder {
            edges: vec![],
            default: Some(Void),
            colors: vec![],
        }
    }
}
impl<Q> TSBuilder<Q, Void> {
    /// Creates an empty instance of `Self`, where edges are uncolored (have color [`Void`])
    pub fn without_edge_colors() -> Self {
        TSBuilder {
            edges: vec![],
            default: None,
            colors: vec![],
        }
    }
}

impl TSBuilder<Void, Void> {
    /// Creates an empty instance of `Self`, where neither states nor edges have a color (i.e. both
    /// are colored [`Void`]).
    pub fn without_colors() -> Self {
        Self {
            edges: vec![],
            default: Some(Void),
            colors: vec![],
        }
    }
}

impl<Q, C> Default for TSBuilder<Q, C> {
    fn default() -> Self {
        Self {
            edges: vec![],
            default: None,
            colors: vec![],
        }
    }
}

impl TSBuilder<bool, Void> {
    /// Tries to turn `self` into a deterministic finite automaton. Panics if `self` is not deterministic.
    pub fn into_dfa(self, initial: usize) -> DFA<CharAlphabet> {
        self.deterministic().with_initial(initial).collect_dfa()
    }
}

impl TSBuilder<Void, usize> {
    /// Attempts to turn `self` into a deterministic parity automaton. Panics if `self` is not deterministic.
    pub fn into_dpa(self, initial: usize) -> DPA<CharAlphabet> {
        self.default_color(Void)
            .deterministic()
            .with_initial(initial)
            .collect_dpa()
    }

    /// Builds a Mealy machine from `self`. Panics if `self` is not deterministic.
    pub fn into_mealy_machine(self, initial: usize) -> MealyMachine<CharAlphabet> {
        self.default_color(Void)
            .deterministic()
            .with_initial(initial)
            .into_mealy()
    }
}

impl<Q: Clone, C: Clone> TSBuilder<Q, C> {
    /// Turns `self` into a [`RightCongruence`] with the given initial state while also erasing all state and edge
    /// colors. Panics if `self` is not deterministic.
    pub fn into_right_congruence_bare(self, initial: usize) -> RightCongruence<CharAlphabet> {
        self.deterministic()
            .with_initial(initial)
            .collect_right_congruence_bare()
    }
}

impl<Q: Clone, C: Clone> TSBuilder<Q, C> {
    /// Sets the default color for states that have no color specified.
    pub fn default_color(mut self, color: Q) -> Self {
        self.default = Some(color);
        self
    }

    /// Adds a list of colors to `self`. The colors are assigned to the states in the order in which they are given.
    /// This means if we give the colors `[true, false]` and then add a transition from state `0` to state `1`, then state
    /// `0` will have color `true` and state `1` will have color `false`.
    pub fn with_colors<I: IntoIterator<Item = Q>>(self, iter: I) -> Self {
        iter.into_iter()
            .enumerate()
            .fold(self, |acc, (i, x)| acc.color(i, x))
    }

    /// Build a deterministic transition system from `self`. Panics if `self` is not deterministic.
    pub fn deterministic(self) -> DTS<CharAlphabet, Q, C> {
        self.collect().try_into().expect("Not deterministic!")
    }

    /// Assigns the given `color` to the state with the given index `idx`.
    pub fn color(mut self, idx: usize, color: Q) -> Self {
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
    ///     .with_colors([true, false]) // colors given in the order of the states
    ///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 0)])
    ///     .into_dfa(0); // 0 is the initial state
    /// ```
    pub fn with_transitions<E: IntoEdge<usize, char, C>, T: IntoIterator<Item = E>>(
        mut self,
        iter: T,
    ) -> Self {
        self.edges.extend(iter.into_iter().map(|t| t.into_edge()));
        self
    }

    /// Adds a list of edges to `self`. The edges are added in the order in which they are given.
    /// The edges can be passed in as anything that is iterable. An easy way is to pass in an array of tuples.
    /// Note, that in comparison to [`Self::with_transitions`], this method adds **edges** and so the individual
    /// elements that are added must store/provide [`Expression`]s instead of [`Symbol`]s.
    ///
    /// This method accepts any iterable yielding objects that implement [`IntoEdge`] for the stored color `C`.
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
    ///     .with_colors([true, false]) // colors given in the order of the states
    ///     .with_edges([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1)])
    ///     .with_edges([(1, 'b', 0)]) // We can also skip the `Void` entry at position 3
    ///     .into_dfa(0); // 0 is the initial state
    /// ```
    pub fn with_edges<E: IntoEdge<usize, char, C>, I: IntoIterator<Item = E>>(
        mut self,
        iter: I,
    ) -> Self {
        self.edges.extend(iter.into_iter().map(|e| e.into_edge()));
        self
    }

    /// Turns `self` into a [`RightCongruence`] with the given initial state. Panics if `self` is not deterministic.
    pub fn into_right_congruence(self, initial: usize) -> RightCongruence<CharAlphabet, Q, C> {
        self.deterministic()
            .with_initial(initial)
            .collect_right_congruence()
    }

    /// Collects self into a non-deterministic transition system.
    pub fn collect(self) -> NTS<CharAlphabet, Q, C> {
        let alphabet = CharAlphabet::from_iter(self.edges.iter().map(|(_, a, _, _)| *a));
        let num_states = self
            .edges
            .iter()
            .flat_map(|(q, _, _, p)| [*p, *q])
            .unique()
            .count();
        let mut ts = NTS::new_for_alphabet(alphabet);
        let colors_it = (0..num_states).map(|x| {
            if let Some(color) =
                self.colors
                    .iter()
                    .find_map(|(q, c)| if *q == x { Some(c.clone()) } else { None })
            {
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

        for (p, a, c, q) in self.edges {
            ts.add_edge(p, a, q, c);
        }
        ts
    }
}
