use std::hash::Hash;

use super::{DefaultIdType, ForAlphabet, IntoEdgeTuple, Sproutable};
use crate::automaton::{DBA, DFA, DPA, MealyMachine, MooreMachine, WithInitial};
use crate::representation::IntoTs;
use crate::{Color, Int, Void, alphabet::CharAlphabet, math::OrderedSet};
use crate::{DTS, NTS, RightCongruence, TS, TransitionSystem};
use itertools::Itertools;
use thiserror::Error;

/// Errors that can occur when turning a [`TSBuilder`] into a transition system or automaton.
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
/// use automata::{Void, ts::TSBuilder};
///
/// let _ts = TSBuilder::default()
///     .with_state_colors([true, false]) // colors given in the order of the states
///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 0)])
///     .into_dfa(0); // 0 is the initial state
/// ```
pub struct TSBuilder<Q = Void, C = Void, const DET: bool = true> {
    symbols: OrderedSet<char>,
    edges: Vec<(DefaultIdType, char, C, DefaultIdType)>,
    default: Option<Q>,
    colors: Vec<(DefaultIdType, Q)>,
}

impl<C, const DET: bool> TSBuilder<Void, C, DET> {
    /// Creates an empty instance of `Self`, where states are uncolored (have color [`Void`])
    pub fn without_state_colors() -> Self {
        TSBuilder {
            symbols: OrderedSet::default(),
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
            symbols: OrderedSet::default(),
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
            symbols: OrderedSet::default(),
            edges: vec![],
            default: Some(Void),
            colors: vec![],
        }
    }
}

impl<Q, C, const DET: bool> Default for TSBuilder<Q, C, DET> {
    fn default() -> Self {
        Self {
            symbols: OrderedSet::default(),
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
    /// - [`BuilderError::MissingStateColor`] if a state has no color and there is no default color,
    /// - [`BuilderError::OverlappingEdge`] if an edge overlaps with a previously added one (this
    ///   can only happen when building a deterministic transition system).
    pub fn try_into_ts<const DOUT: bool>(
        self,
    ) -> Result<TS<CharAlphabet, Q, C, DOUT>, BuilderError> {
        let alphabet =
            CharAlphabet::from_iter(self.edges.iter().map(|(_, c, _, _)| *c).chain(self.symbols));

        let num_states = self
            .edges
            .iter()
            .flat_map(|(q, _, _, p)| [*p, *q])
            .unique()
            .count();
        let mut ts = TS::for_alphabet_size_hint(alphabet, num_states);

        for i in 0..num_states {
            let i = i as DefaultIdType;
            let color = self
                .colors
                .iter()
                .find_map(|(q, c)| (*q == i).then(|| c.clone()))
                .or_else(|| self.default.clone())
                .ok_or(BuilderError::MissingStateColor(i))?;
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
    /// use automata::{Void, ts::TSBuilder};
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
    /// use automata::{Void, ts::TSBuilder};
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
}

impl<Q: Color, C: Color> TSBuilder<Q, C, true> {
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
    ) -> WithInitial<DTS<CharAlphabet, Q, C>>
    where
        C: Hash + Eq,
    {
        or_panic(self.try_into_dts_with_initial(initial))
    }

    /// Fallible version of [`Self::into_dts_with_initial`].
    pub fn try_into_dts_with_initial(
        self,
        initial: DefaultIdType,
    ) -> Result<WithInitial<DTS<CharAlphabet, Q, C>>, BuilderError>
    where
        C: Hash + Eq,
    {
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
    ) -> RightCongruence<CharAlphabet, Q, C> {
        or_panic(self.try_into_right_congruence(initial))
    }

    /// Fallible version of [`Self::into_right_congruence`].
    pub fn try_into_right_congruence(
        self,
        initial: DefaultIdType,
    ) -> Result<RightCongruence<CharAlphabet, Q, C>, BuilderError> {
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
    ) -> RightCongruence<CharAlphabet> {
        or_panic(self.try_into_right_congruence_bare(initial))
    }

    /// Fallible version of [`Self::into_right_congruence_bare`].
    pub fn try_into_right_congruence_bare(
        self,
        initial: DefaultIdType,
    ) -> Result<RightCongruence<CharAlphabet>, BuilderError> {
        Ok(self
            .try_into_dts()?
            .with_initial(initial)
            .erase_state_colors()
            .erase_edge_colors()
            .into_right_congruence())
    }
}

impl TSBuilder<bool, Void, true> {
    /// Turns `self` into a deterministic finite automaton.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_dfa(self, initial: DefaultIdType) -> DFA<CharAlphabet> {
        or_panic(self.try_into_dfa(initial))
    }

    /// Fallible version of [`Self::into_dfa`].
    pub fn try_into_dfa(self, initial: DefaultIdType) -> Result<DFA<CharAlphabet>, BuilderError> {
        Ok(self.try_into_dts()?.with_initial(initial).into_dfa())
    }
}

impl TSBuilder<Void, bool, true> {
    /// Turns `self` into a deterministic Büchi automaton.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_dba(self, initial: DefaultIdType) -> DBA<CharAlphabet> {
        or_panic(self.try_into_dba(initial))
    }

    /// Fallible version of [`Self::into_dba`].
    pub fn try_into_dba(self, initial: DefaultIdType) -> Result<DBA<CharAlphabet>, BuilderError> {
        Ok(self
            .default_color(Void)
            .try_into_dts()?
            .with_initial(initial)
            .into_dba())
    }
}

impl TSBuilder<Void, Int, true> {
    /// Turns `self` into a deterministic parity automaton.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_dpa(self, initial: DefaultIdType) -> DPA<CharAlphabet> {
        or_panic(self.try_into_dpa(initial))
    }

    /// Fallible version of [`Self::into_dpa`].
    pub fn try_into_dpa(self, initial: DefaultIdType) -> Result<DPA<CharAlphabet>, BuilderError> {
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
    pub fn into_mealy(self, initial: DefaultIdType) -> MealyMachine<CharAlphabet> {
        or_panic(self.try_into_mealy(initial))
    }

    /// Fallible version of [`Self::into_mealy`].
    pub fn try_into_mealy(
        self,
        initial: DefaultIdType,
    ) -> Result<MealyMachine<CharAlphabet>, BuilderError> {
        Ok(self
            .default_color(Void)
            .try_into_dts()?
            .with_initial(initial)
            .into_mealy())
    }
}

impl TSBuilder<Int, Void, true> {
    /// Builds a Moore machine from `self`.
    ///
    /// # Panics
    /// Panics if the builder is inconsistent, see [`Self::try_into_ts`].
    #[track_caller]
    pub fn into_moore(self, initial: DefaultIdType) -> MooreMachine<CharAlphabet> {
        or_panic(self.try_into_moore(initial))
    }

    /// Fallible version of [`Self::into_moore`].
    pub fn try_into_moore(
        self,
        initial: DefaultIdType,
    ) -> Result<MooreMachine<CharAlphabet>, BuilderError> {
        Ok(self.try_into_dts()?.with_initial(initial).into_moore())
    }
}

#[cfg(test)]
mod tests {
    use super::{BuilderError, TSBuilder};

    #[test]
    fn building_reports_missing_state_colors() {
        // state 1 has no color and there is no default
        let builder = TSBuilder::without_edge_colors()
            .color(0, true)
            .with_transitions([(0, 'a', 1), (1, 'a', 0)]);
        assert_eq!(
            builder.try_into_dfa(0).err(),
            Some(BuilderError::MissingStateColor(1))
        );

        let with_default = TSBuilder::without_edge_colors()
            .color(0, true)
            .default_color(false)
            .with_transitions([(0, 'a', 1), (1, 'a', 0)]);
        assert!(with_default.try_into_dfa(0).is_ok());
    }

    #[test]
    fn building_reports_overlapping_edges() {
        let builder = TSBuilder::without_colors().with_transitions([(0, 'a', 1), (0, 'a', 0)]);
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
        let nondeterministic = TSBuilder::<crate::Void, crate::Void, false>::without_colors()
            .with_transitions([(0, 'a', 1), (0, 'a', 0)])
            .try_into_nts();
        assert!(nondeterministic.is_ok());
    }

    #[test]
    #[should_panic(expected = "has no color")]
    fn into_panics_where_try_into_returns_an_error() {
        let _ = TSBuilder::without_edge_colors()
            .color(0, true)
            .with_transitions([(0, 'a', 1)])
            .into_dfa(0);
    }
}
