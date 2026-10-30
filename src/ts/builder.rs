use super::{DefaultIdType, ForAlphabet, IntoEdgeTuple, Sproutable, Storage};
use crate::automaton::{Automaton, DBA, DFA, DPA, MealyMachine, MooreMachine, WithInitial};
use crate::automaton::{
    BuchiCondition, MealySemantics, MinEvenParityCondition, MooreSemantics, ReachabilityCondition,
};
use crate::representation::IntoTs;
use crate::{Color, Int, Void, alphabet::CharAlphabet};
use crate::{DTS, NTS, RightCongruence, TransitionSystem};
use std::collections::{BTreeSet, HashMap};
use thiserror::Error;

/// Errors that can occur when turning a [`Builder`] into a transition system or automaton.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum BuilderError {
    /// A state has no color and no default color was given.
    #[error(
        "state {0} has no color: set one with `color` or `with_state_colors`, or provide a `default_color`"
    )]
    MissingStateColor(DefaultIdType),
    /// An added edge overlaps with an edge that was added before.
    #[error(
        "the edge from {source_state} on {expression} to {target} overlaps with an existing edge to {existing_target}"
    )]
    OverlappingEdge {
        /// The source state of the edge that could not be added.
        source_state: DefaultIdType,
        /// The expression (symbol) on the edge.
        expression: String,
        /// The target state of the edge that could not be added.
        target: DefaultIdType,
        /// The target of the existing edge with which it overlaps.
        existing_target: DefaultIdType,
    },
}

#[track_caller]
fn or_panic<T>(result: Result<T, BuilderError>) -> T {
    result.unwrap_or_else(|error| panic!("{error}"))
}

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
///
/// Further, state 0 should be initial and colored `true` and state 1 should be colored `false`. This can be done as follows
/// ```
/// use automata::{Void, ts::Builder};
///
/// let _ts = Builder::default()
///     .with_state_colors([true, false]) // colors given in the order of the states
///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 0)])
///     .into_dfa(0); // 0 is the initial state
/// ```
pub struct Builder<Q = Void, C = Void> {
    symbols: BTreeSet<char>,
    edges: Vec<(DefaultIdType, char, C, DefaultIdType)>,
    default: Option<Q>,
    colors: Vec<(DefaultIdType, Q)>,
}

impl<C> Builder<Void, C> {
    /// Creates an empty instance of `Self`, where states are uncolored (have color [`Void`])
    pub fn without_state_colors() -> Self {
        Builder {
            symbols: BTreeSet::default(),
            edges: vec![],
            default: Some(Void),
            colors: vec![],
        }
    }
}
impl<Q> Builder<Q, Void> {
    /// Creates an empty instance of `Self`, where edges are uncolored (have color [`Void`])
    pub fn without_edge_colors() -> Self {
        Builder {
            symbols: BTreeSet::default(),
            edges: vec![],
            default: None,
            colors: vec![],
        }
    }
}

impl Builder<Void, Void> {
    /// Creates an empty instance of `Self`, where neither states nor edges have a color (i.e. both
    /// are colored [`Void`]).
    pub fn without_colors() -> Self {
        Self {
            symbols: BTreeSet::default(),
            edges: vec![],
            default: Some(Void),
            colors: vec![],
        }
    }
}

impl<Q, C> Default for Builder<Q, C> {
    fn default() -> Self {
        Self {
            symbols: BTreeSet::default(),
            edges: vec![],
            default: None,
            colors: vec![],
        }
    }
}

impl<Q: Color, C: Color> Builder<Q, C> {
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

    /// Builds the transition system `T` from `self`. The target type decides about determinism:
    /// for a deterministic one (like [`DTS`] or [`DenseTs`](super::DenseTs)) overlapping edges are an
    /// error, a non-deterministic one (like [`NTS`]) accepts them.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_build`].
    ///
    /// # Example
    /// ```
    /// use automata::{DTS, ts::Builder};
    ///
    /// let builder = Builder::without_colors().with_edges([(0, 'a', 1), (1, 'a', 0)]);
    /// let _dts = builder.build::<DTS>();
    /// ```
    #[track_caller]
    pub fn build<T>(self) -> T
    where
        T: ForAlphabet<CharAlphabet>
            + Sproutable<
                Alphabet = CharAlphabet,
                StateIndex = DefaultIdType,
                StateColor = Q,
                EdgeColor = C,
            >,
    {
        or_panic(self.try_build())
    }

    /// Fallible version of [`Self::build`]. The states are `0..=m` where `m` is the largest id
    /// that appears on an edge, and the alphabet consists of the symbols on the edges
    /// and the ones added with [`Self::with_alphabet_symbols`].
    ///
    /// # Errors
    /// - [`BuilderError::MissingStateColor`] if a state has no color and there is no default color
    ///   (so gaps in the ids need a default color),
    /// - [`BuilderError::OverlappingEdge`] if `T` is deterministic and an edge overlaps with a
    ///   previously added one.
    pub fn try_build<T>(self) -> Result<T, BuilderError>
    where
        T: ForAlphabet<CharAlphabet>
            + Sproutable<
                Alphabet = CharAlphabet,
                StateIndex = DefaultIdType,
                StateColor = Q,
                EdgeColor = C,
            >,
    {
        let alphabet =
            CharAlphabet::from_iter(self.edges.iter().map(|(_, c, _, _)| *c).chain(self.symbols));

        // state ids need not be contiguous: there is a state for every id up to the maximal one
        let num_states = self
            .edges
            .iter()
            .flat_map(|(q, _, _, p)| [*p, *q])
            .max()
            .map_or(0, |max| max as usize + 1);
        let mut ts = T::for_alphabet_size_hint(alphabet, num_states);

        // if a state is given a color multiple times, the first one counts
        let mut colors: Vec<Option<Q>> = vec![None; num_states];
        for (q, c) in self.colors {
            if let Some(slot @ None) = colors.get_mut(q as usize) {
                *slot = Some(c);
            }
        }
        for (i, color) in colors.into_iter().enumerate() {
            let color = color
                .or_else(|| self.default.clone())
                .ok_or(BuilderError::MissingStateColor(i as DefaultIdType))?;
            ts.add_state(color);
        }

        if <<T as Sproutable>::Storage as Storage<CharAlphabet>>::DETERMINISTIC {
            let mut seen = HashMap::<(DefaultIdType, char), DefaultIdType>::new();
            for &(q, e, _, p) in &self.edges {
                if let Some(existing_target) = seen.insert((q, e), p) {
                    return Err(BuilderError::OverlappingEdge {
                        source_state: q,
                        expression: e.to_string(),
                        target: p,
                        existing_target,
                    });
                }
            }
        }

        // linked storages iterate the edges of a state in reverse order of insertion, so we insert
        // them back to front to get them in the order in which they were given
        for edge in self.edges.into_iter().rev() {
            ts.add_edge(edge);
        }
        Ok(ts)
    }

    /// Builds a [NondeterministicTransitionSystem](`NTS`) from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_nts(self) -> NTS<CharAlphabet, Q, C> {
        or_panic(self.try_into_nts())
    }

    /// Fallible version of [`Self::into_nts`].
    pub fn try_into_nts(self) -> Result<NTS<CharAlphabet, Q, C>, BuilderError> {
        self.try_build()
    }

    /// Builds a [NondeterministicTransitionSystem](`NTS`) from `self` with an initial state.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_nts_with_initial(
        self,
        initial: DefaultIdType,
    ) -> WithInitial<NTS<CharAlphabet, Q, C>> {
        or_panic(self.try_into_nts_with_initial(initial))
    }

    /// Fallible version of [`Self::into_nts_with_initial`].
    pub fn try_into_nts_with_initial(
        self,
        initial: DefaultIdType,
    ) -> Result<WithInitial<NTS<CharAlphabet, Q, C>>, BuilderError> {
        Ok(self.try_into_nts()?.with_initial(initial))
    }

    /// Assigns the given `color` to the state with the given index `idx`.
    ///
    /// # Panics
    ///
    /// Panics if the state `idx` already has a color.
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
    ///
    /// Further, state 0 should be initial and colored `true` and state 1 should be colored `false`. This can be done as follows
    /// ```
    /// use automata::{Void, ts::Builder};
    ///
    /// let ts = Builder::default()
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
    /// elements that are added must store/provide [`crate::alphabet::Expression`]s instead of [`crate::alphabet::Symbol`]s.
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
    ///
    /// Further, state 0 should be initial and colored `true` and state 1 should be colored `false`. This can be done as follows
    /// ```
    /// use automata::{Void, ts::Builder};
    ///
    /// let ts = Builder::default()
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
}

impl<Q: Color, C: Color> Builder<Q, C> {
    /// Builds an instance of [`DTS`] from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_dts(self) -> DTS<CharAlphabet, Q, C> {
        or_panic(self.try_into_dts())
    }

    /// Fallible version of [`Self::into_dts`].
    ///
    /// # Errors
    /// - [`BuilderError::MissingStateColor`] if a state has no color and there is no default color
    ///   (the states are `0..=m` where `m` is the largest id, so gaps in the ids need a default
    ///   color),
    /// - [`BuilderError::OverlappingEdge`] if an edge overlaps with a previously added one.
    pub fn try_into_dts(self) -> Result<DTS<CharAlphabet, Q, C>, BuilderError> {
        self.try_build()
    }

    /// Builds an instance of [`DTS`] from `self` and sets the given `initial` state
    /// as the designated initial state of the output object.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_dts_with_initial(
        self,
        initial: DefaultIdType,
    ) -> WithInitial<DTS<CharAlphabet, Q, C>> {
        or_panic(self.try_into_dts_with_initial(initial))
    }

    /// Fallible version of [`Self::into_dts_with_initial`].
    pub fn try_into_dts_with_initial(
        self,
        initial: DefaultIdType,
    ) -> Result<WithInitial<DTS<CharAlphabet, Q, C>>, BuilderError> {
        Ok(self.try_into_dts()?.with_initial(initial))
    }

    /// Builds an [`Automaton`] with the given `initial` state and `acceptance` over a [`DTS`]. The
    /// helpers [`Self::into_dfa`], [`Self::into_dba`], [`Self::into_dpa`], [`Self::into_moore`] and
    /// [`Self::into_mealy`] are shorthands for the common acceptance conditions.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_build`].
    ///
    /// # Example
    /// ```
    /// use automata::{automaton::ReachabilityCondition, ts::Builder};
    ///
    /// let dfa = Builder::without_edge_colors()
    ///     .with_state_colors([true, false])
    ///     .with_edges([(0, 'a', 1), (1, 'a', 0)])
    ///     .into_automaton(0, ReachabilityCondition);
    /// assert!(dfa.accepts("aa"));
    /// ```
    #[track_caller]
    pub fn into_automaton<Sem>(
        self,
        initial: DefaultIdType,
        acceptance: Sem,
    ) -> Automaton<DTS<CharAlphabet, Q, C>, Sem> {
        or_panic(self.try_into_automaton(initial, acceptance))
    }

    /// Fallible version of [`Self::into_automaton`].
    ///
    /// # Errors
    /// See [`Self::try_build`].
    pub fn try_into_automaton<Sem>(
        self,
        initial: DefaultIdType,
        acceptance: Sem,
    ) -> Result<Automaton<DTS<CharAlphabet, Q, C>, Sem>, BuilderError> {
        Ok(Automaton::from_parts_with_acceptance(
            self.try_build()?,
            initial,
            acceptance,
        ))
    }

    /// Turns `self` into a [`RightCongruence`] with the given initial state.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_right_congruence(
        self,
        initial: DefaultIdType,
    ) -> RightCongruence<DTS<CharAlphabet, Q, C>> {
        or_panic(self.try_into_right_congruence(initial))
    }

    /// Fallible version of [`Self::into_right_congruence`].
    pub fn try_into_right_congruence(
        self,
        initial: DefaultIdType,
    ) -> Result<RightCongruence<DTS<CharAlphabet, Q, C>>, BuilderError> {
        Ok(self
            .try_into_dts()?
            .with_initial(initial)
            .into_right_congruence())
    }

    /// Turns `self` into a [`RightCongruence`] with the given initial state while also erasing all state and edge
    /// colors.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_right_congruence_bare(
        self,
        initial: DefaultIdType,
    ) -> RightCongruence<DTS<CharAlphabet, Void, Void>> {
        or_panic(self.try_into_right_congruence_bare(initial))
    }

    /// Fallible version of [`Self::into_right_congruence_bare`].
    pub fn try_into_right_congruence_bare(
        self,
        initial: DefaultIdType,
    ) -> Result<RightCongruence<DTS<CharAlphabet, Void, Void>>, BuilderError> {
        Ok(self
            .try_into_dts()?
            .with_initial(initial)
            .erase_state_colors()
            .erase_edge_colors()
            .into_right_congruence())
    }
}

impl Builder<bool, Void> {
    /// Turns `self` into a deterministic finite automaton.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_dfa(self, initial: DefaultIdType) -> DFA<DTS<CharAlphabet, bool, Void>> {
        or_panic(self.try_into_dfa(initial))
    }

    /// Fallible version of [`Self::into_dfa`].
    pub fn try_into_dfa(
        self,
        initial: DefaultIdType,
    ) -> Result<DFA<DTS<CharAlphabet, bool, Void>>, BuilderError> {
        self.try_into_automaton(initial, ReachabilityCondition)
    }
}

impl Builder<Void, bool> {
    /// Turns `self` into a deterministic Büchi automaton.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_dba(self, initial: DefaultIdType) -> DBA<DTS<CharAlphabet, Void, bool>> {
        or_panic(self.try_into_dba(initial))
    }

    /// Fallible version of [`Self::into_dba`].
    pub fn try_into_dba(
        self,
        initial: DefaultIdType,
    ) -> Result<DBA<DTS<CharAlphabet, Void, bool>>, BuilderError> {
        self.default_color(Void)
            .try_into_automaton(initial, BuchiCondition)
    }
}

impl Builder<Void, Int> {
    /// Turns `self` into a deterministic parity automaton.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_dpa(self, initial: DefaultIdType) -> DPA<DTS<CharAlphabet, Void, Int>> {
        or_panic(self.try_into_dpa(initial))
    }

    /// Fallible version of [`Self::into_dpa`].
    pub fn try_into_dpa(
        self,
        initial: DefaultIdType,
    ) -> Result<DPA<DTS<CharAlphabet, Void, Int>>, BuilderError> {
        self.default_color(Void)
            .try_into_automaton(initial, MinEvenParityCondition)
    }

    /// Builds a Mealy machine from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_mealy(self, initial: DefaultIdType) -> MealyMachine<DTS<CharAlphabet, Void, Int>> {
        or_panic(self.try_into_mealy(initial))
    }

    /// Fallible version of [`Self::into_mealy`].
    pub fn try_into_mealy(
        self,
        initial: DefaultIdType,
    ) -> Result<MealyMachine<DTS<CharAlphabet, Void, Int>>, BuilderError> {
        self.default_color(Void)
            .try_into_automaton(initial, MealySemantics)
    }
}

impl Builder<Int, Void> {
    /// Builds a Moore machine from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_dts`].
    #[track_caller]
    pub fn into_moore(self, initial: DefaultIdType) -> MooreMachine<DTS<CharAlphabet, Int, Void>> {
        or_panic(self.try_into_moore(initial))
    }

    /// Fallible version of [`Self::into_moore`].
    pub fn try_into_moore(
        self,
        initial: DefaultIdType,
    ) -> Result<MooreMachine<DTS<CharAlphabet, Int, Void>>, BuilderError> {
        self.try_into_automaton(initial, MooreSemantics)
    }
}

#[cfg(test)]
mod tests {
    use super::{Builder, BuilderError};
    use crate::TransitionSystem;
    use crate::alphabet::CharAlphabet;
    use crate::ts::States;

    #[test]
    fn non_contiguous_state_ids_with_default_color() {
        let ts = Builder::<_, _>::without_edge_colors()
            .default_color(false)
            .color(5, true)
            .with_transitions([(0, 'a', 5)])
            .try_into_nts()
            .unwrap();
        assert_eq!(ts.states().count(), 6);
        assert_eq!(ts.state_color(5).as_deref(), Some(&true));
        assert_eq!(ts.state_color(3).as_deref(), Some(&false));
    }

    #[test]
    fn non_contiguous_state_ids_without_default_color() {
        // the gap states 1..=4 have no color
        let builder = Builder::<_, _>::without_edge_colors()
            .color(0, true)
            .color(5, true)
            .with_transitions([(0, 'a', 5)]);
        assert_eq!(
            builder.try_into_nts().err(),
            Some(BuilderError::MissingStateColor(1))
        );
    }

    #[test]
    fn building_reports_missing_state_colors() {
        // state 1 has no color and there is no default
        let builder = Builder::without_edge_colors()
            .color(0, true)
            .with_transitions([(0, 'a', 1), (1, 'a', 0)]);
        assert_eq!(
            builder.try_into_dfa(0).err(),
            Some(BuilderError::MissingStateColor(1))
        );

        let with_default = Builder::without_edge_colors()
            .color(0, true)
            .default_color(false)
            .with_transitions([(0, 'a', 1), (1, 'a', 0)]);
        assert!(with_default.try_into_dfa(0).is_ok());
    }

    #[test]
    fn building_reports_overlapping_edges() {
        let builder = Builder::without_colors().with_transitions([(0, 'a', 1), (0, 'a', 0)]);
        assert_eq!(
            builder.try_into_dts().err(),
            Some(BuilderError::OverlappingEdge {
                source_state: 0,
                expression: "a".to_string(),
                target: 0,
                existing_target: 1,
            })
        );
        // the same edges are fine in a nondeterministic transition system
        let nondeterministic = Builder::<crate::Void, crate::Void>::without_colors()
            .with_transitions([(0, 'a', 1), (0, 'a', 0)])
            .try_into_nts();
        assert!(nondeterministic.is_ok());
    }

    #[test]
    fn build_decides_about_determinism_by_the_target_type() {
        use crate::{
            DTS, NTS, Void,
            ts::{DenseTs, Det, LinkedTs},
        };
        let builder =
            || Builder::<Void, Void>::without_colors().with_transitions([(0, 'a', 1), (0, 'a', 0)]);
        assert!(builder().try_build::<NTS>().is_ok());
        let overlap = BuilderError::OverlappingEdge {
            source_state: 0,
            expression: "a".to_string(),
            target: 0,
            existing_target: 1,
        };
        assert_eq!(builder().try_build::<DTS>().err(), Some(overlap.clone()));
        assert_eq!(
            builder()
                .try_build::<DenseTs<CharAlphabet, Void, Void>>()
                .err(),
            Some(overlap)
        );
        let _: Det<LinkedTs<CharAlphabet, Void, Void>> = Builder::without_colors()
            .with_edges([(0, 'a', 1), (1, 'a', 0)])
            .build();
    }

    #[test]
    fn built_systems_iterate_edges_in_the_order_they_were_given() {
        use crate::{DTS, NTS, TransitionSystem};
        let edges = [(0, 'a', 1), (0, 'b', 0), (0, 'c', 1), (1, 'a', 0)];
        let expected: Vec<_> = edges.iter().filter(|e| e.0 == 0).map(|e| e.1).collect();
        let nts = Builder::without_colors().with_edges(edges).build::<NTS>();
        let dts = Builder::without_colors().with_edges(edges).build::<DTS>();
        let nts: Vec<char> = nts
            .edges_from(0)
            .unwrap()
            .map(|e| *e.expression())
            .collect();
        let dts: Vec<char> = dts
            .edges_from(0)
            .unwrap()
            .map(|e| *e.expression())
            .collect();
        assert_eq!(nts, expected);
        assert_eq!(dts, expected);
    }

    #[test]
    #[should_panic(expected = "has no color")]
    fn into_panics_where_try_into_returns_an_error() {
        let _ = Builder::without_edge_colors()
            .color(0, true)
            .with_transitions([(0, 'a', 1)])
            .into_dfa(0);
    }
}
