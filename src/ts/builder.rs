use super::{DefaultIdType, ForAlphabet, IntoEdgeTuple, Sproutable};
use crate::automaton::{DBA, DFA, DPA, MealyMachine, MooreMachine, WithInitial};
use crate::representation::IntoTs;
use crate::{Color, Int, Void, alphabet::CharAlphabet};
use crate::{DTS, NTS, RightCongruence, TS, TransitionSystem};
use std::collections::BTreeSet;
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
pub struct Builder<Q = Void, C = Void, const DET: bool = true> {
    symbols: BTreeSet<char>,
    edges: Vec<(DefaultIdType, char, C, DefaultIdType)>,
    default: Option<Q>,
    colors: Vec<(DefaultIdType, Q)>,
}

impl<C, const DET: bool> Builder<Void, C, DET> {
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
impl<Q, const DET: bool> Builder<Q, Void, DET> {
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

impl<const DET: bool> Builder<Void, Void, DET> {
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

impl<Q, C, const DET: bool> Default for Builder<Q, C, DET> {
    fn default() -> Self {
        Self {
            symbols: BTreeSet::default(),
            edges: vec![],
            default: None,
            colors: vec![],
        }
    }
}

impl<Q: Color, C: Color, const DET: bool> Builder<Q, C, DET> {
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

    /// Creates an instance of a non-deterministic [`TS`] from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_ts<const DOUT: bool>(self) -> TS<CharAlphabet, Q, C, DOUT> {
        or_panic(self.try_into_ts())
    }

    /// Creates an instance of a [`TS`] from `self`.
    ///
    /// # Errors
    /// - [`BuilderError::MissingStateColor`] if a state has no color and there is no default color
    ///   (the states are `0..=m` where `m` is the largest id, so gaps in the ids need a default
    ///   color),
    /// - [`BuilderError::OverlappingEdge`] if an edge overlaps with a previously added one (this
    ///   can only happen when building a deterministic transition system).
    pub fn try_into_ts<const DOUT: bool>(
        self,
    ) -> Result<TS<CharAlphabet, Q, C, DOUT>, BuilderError> {
        let alphabet =
            CharAlphabet::from_iter(self.edges.iter().map(|(_, c, _, _)| *c).chain(self.symbols));

        // state ids need not be contiguous: there is a state for every id up to the maximal one
        let num_states = self
            .edges
            .iter()
            .flat_map(|(q, _, _, p)| [*p, *q])
            .max()
            .map_or(0, |max| max as usize + 1);
        let mut ts = TS::for_alphabet_size_hint(alphabet, num_states);

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

        for (q, e, c, p) in self.edges {
            if let Some((_, _, _, existing_target)) = ts.add_edge((q, e, c, p)) {
                return Err(BuilderError::OverlappingEdge {
                    source_state: q,
                    expression: e.to_string(),
                    target: p,
                    existing_target,
                });
            }
        }
        Ok(ts)
    }

    /// Builds a [NondeterministicTransitionSystem](`NTS`) from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_nts(self) -> NTS<CharAlphabet, Q, C> {
        or_panic(self.try_into_nts())
    }

    /// Fallible version of [`Self::into_nts`].
    pub fn try_into_nts(self) -> Result<NTS<CharAlphabet, Q, C>, BuilderError> {
        self.try_into_ts()
    }

    /// Builds a [NondeterministicTransitionSystem](`NTS`) from `self` with an initial state.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
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
        Ok(self.try_into_ts()?.with_initial(initial))
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

impl<Q: Color, C: Color> Builder<Q, C, true> {
    /// Builds an instance of [`DTS`] from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_dts(self) -> DTS<CharAlphabet, Q, C> {
        or_panic(self.try_into_dts())
    }

    /// Fallible version of [`Self::into_dts`].
    pub fn try_into_dts(self) -> Result<DTS<CharAlphabet, Q, C>, BuilderError> {
        self.try_into_ts()
    }

    /// Builds an instance of [`DTS`] from `self` and sets the given `initial` state
    /// as the designated initial state of the output object.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
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

    /// Turns `self` into a [`RightCongruence`] with the given initial state.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
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
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
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

impl Builder<bool, Void, true> {
    /// Turns `self` into a deterministic finite automaton.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_dfa(self, initial: DefaultIdType) -> DFA<DTS<CharAlphabet, bool, Void>> {
        or_panic(self.try_into_dfa(initial))
    }

    /// Fallible version of [`Self::into_dfa`].
    pub fn try_into_dfa(
        self,
        initial: DefaultIdType,
    ) -> Result<DFA<DTS<CharAlphabet, bool, Void>>, BuilderError> {
        Ok(self.try_into_dts()?.with_initial(initial).into_dfa())
    }
}

impl Builder<Void, bool, true> {
    /// Turns `self` into a deterministic Büchi automaton.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_dba(self, initial: DefaultIdType) -> DBA<DTS<CharAlphabet, Void, bool>> {
        or_panic(self.try_into_dba(initial))
    }

    /// Fallible version of [`Self::into_dba`].
    pub fn try_into_dba(
        self,
        initial: DefaultIdType,
    ) -> Result<DBA<DTS<CharAlphabet, Void, bool>>, BuilderError> {
        Ok(self
            .default_color(Void)
            .try_into_dts()?
            .with_initial(initial)
            .into_dba())
    }
}

impl Builder<Void, Int, true> {
    /// Turns `self` into a deterministic parity automaton.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_dpa(self, initial: DefaultIdType) -> DPA<DTS<CharAlphabet, Void, Int>> {
        or_panic(self.try_into_dpa(initial))
    }

    /// Fallible version of [`Self::into_dpa`].
    pub fn try_into_dpa(
        self,
        initial: DefaultIdType,
    ) -> Result<DPA<DTS<CharAlphabet, Void, Int>>, BuilderError> {
        Ok(self
            .default_color(Void)
            .try_into_dts()?
            .with_initial(initial)
            .into_dpa())
    }

    /// Builds a Mealy machine from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_mealy(self, initial: DefaultIdType) -> MealyMachine<DTS<CharAlphabet, Void, Int>> {
        or_panic(self.try_into_mealy(initial))
    }

    /// Fallible version of [`Self::into_mealy`].
    pub fn try_into_mealy(
        self,
        initial: DefaultIdType,
    ) -> Result<MealyMachine<DTS<CharAlphabet, Void, Int>>, BuilderError> {
        Ok(self
            .default_color(Void)
            .try_into_dts()?
            .with_initial(initial)
            .into_mealy())
    }
}

impl Builder<Int, Void, true> {
    /// Builds a Moore machine from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_moore(self, initial: DefaultIdType) -> MooreMachine<DTS<CharAlphabet, Int, Void>> {
        or_panic(self.try_into_moore(initial))
    }

    /// Fallible version of [`Self::into_moore`].
    pub fn try_into_moore(
        self,
        initial: DefaultIdType,
    ) -> Result<MooreMachine<DTS<CharAlphabet, Int, Void>>, BuilderError> {
        Ok(self.try_into_dts()?.with_initial(initial).into_moore())
    }
}

#[cfg(test)]
mod tests {
    use super::{Builder, BuilderError};
    use crate::TransitionSystem;
    use crate::ts::States;

    #[test]
    fn non_contiguous_state_ids_with_default_color() {
        let ts = Builder::<_, _, false>::without_edge_colors()
            .default_color(false)
            .color(5, true)
            .with_transitions([(0, 'a', 5)])
            .try_into_nts()
            .unwrap();
        assert_eq!(ts.state_indices().count(), 6);
        assert_eq!(ts.state_color(5).as_deref(), Some(&true));
        assert_eq!(ts.state_color(3).as_deref(), Some(&false));
    }

    #[test]
    fn non_contiguous_state_ids_without_default_color() {
        // the gap states 1..=4 have no color
        let builder = Builder::<_, _, false>::without_edge_colors()
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
        let nondeterministic = Builder::<crate::Void, crate::Void, false>::without_colors()
            .with_transitions([(0, 'a', 1), (0, 'a', 0)])
            .try_into_nts();
        assert!(nondeterministic.is_ok());
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
