use std::collections::BTreeSet;

use crate::prelude::*;

use super::StatesWithColor;

#[derive(Clone, Copy, Default, Hash, Eq, PartialEq)]
pub struct DFASemantics;

impl std::fmt::Debug for DFASemantics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DFA (reach true)")
    }
}

impl<C> FiniteSemantics<bool, C> for DFASemantics {
    type Output = bool;
    fn finite_semantic<R>(&self, run: R) -> Self::Output
    where
        R: FiniteRun<StateColor = bool, EdgeColor = C>,
    {
        run.state_colors()
            .and_then(|colors| colors.last())
            .unwrap_or(false)
    }
}

/// A deterministic finite automaton (DFA) is a deterministic automaton with a simple acceptance condition. It accepts a finite word if it reaches an accepting state.
pub type DFA<A = CharAlphabet> = Automaton<Initialized<DTS<A, bool, Void>>, DFASemantics, false>;
/// Helper trait for creating a [`DFA`] from a given transition system.
pub type IntoDFA<T> = Automaton<T, DFASemantics, false>;

impl<D> IntoDFA<D>
where
    D: Deterministic<StateColor = bool>,
{
    /// Returns the indices of all states that are accepting.
    pub fn accepting_states(&self) -> StatesWithColor<'_, Self> {
        StatesWithColor::new(self, true)
    }

    /// Returns the indices of all states that are rejecting.
    pub fn rejecting_states(&self) -> StatesWithColor<'_, Self> {
        StatesWithColor::new(self, false)
    }

    /// Checks whether `self` is equivalent to `other`, i.e. whether the two DFAs accept
    /// the same language. This is done by negating `self` and then verifying that the intersection
    /// of the negated automaton with `other` is empty.
    pub fn equivalent<E>(&self, other: E) -> bool
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool>,
    {
        self.negation().intersection(other).is_empty_language()
    }

    /// Tries to construct a (finite) word witnessing that the accepted language is empty. If such a word exists,
    /// the function returns it, otherwise `None`.
    pub fn give_word(&self) -> Option<Vec<SymbolOf<Self>>> {
        self.minimal_representatives().find_map(|(mr, index)| {
            if self
                .state_color(index)
                .expect("Every state must be colored")
            {
                Some(mr)
            } else {
                None
            }
        })
    }

    /// Returns true if and only if the accepted language is empty.
    pub fn is_empty_language(&self) -> bool {
        self.give_word().is_none()
    }

    /// Computes the union of `self` with the given `other` object (that can be viewed as a DFA) through
    /// a simple product construction.
    pub fn union<'a, E>(
        &'a self,
        other: E,
    ) -> IntoDFA<impl Deterministic<Alphabet = D::Alphabet, StateColor = bool> + 'a>
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool> + 'a,
    {
        self.ts_product(other)
            .map_state_colors(|(a, b)| a || b)
            .into()
    }

    /// Computes the intersection of `self` with the given `other` object (that can be viewed as a DFA) through
    /// a simple product construction.
    pub fn intersection<'a, E>(
        &'a self,
        other: E,
    ) -> IntoDFA<impl Deterministic<Alphabet = D::Alphabet, StateColor = bool> + 'a>
    where
        E: Congruence<Alphabet = D::Alphabet, StateColor = bool> + 'a,
    {
        self.ts_product(other)
            .map_state_colors(|(a, b)| a && b)
            .into()
    }

    /// Computes the negation of `self` by swapping accepting and non-accepting states.
    pub fn negation(
        &self,
    ) -> IntoDFA<impl Deterministic<Alphabet = D::Alphabet, StateColor = bool> + '_> {
        self.map_state_colors(|x| !x).into()
    }

    /// Attempts to separate the state `left` from the state `right` by finding a word that leads to different colors.
    /// For a [`DFA`], this means that the returned word is in the symmetric difference of
    /// the languages accepted by the two states.
    pub fn separate<X, Y>(&self, left: X, right: Y) -> Option<Vec<SymbolOf<Self>>>
    where
        X: Indexes<Self>,
        Y: Indexes<Self>,
    {
        let q = left.to_index(self)?;
        let p = right.to_index(self)?;
        if p == q {
            return None;
        }

        self.with_initial(q)
            .ts_product(self.with_initial(p))
            .minimal_representatives()
            .find_map(|(rep, ProductIndex(l, r))| {
                if self.state_color(l).unwrap() != self.state_color(r).unwrap() {
                    Some(rep)
                } else {
                    None
                }
            })
    }
}

/// Helper trait to convert from boolean to usize. Normally, a `true` value corresponds to `1`, while
/// a `false` value corresponds to `0`. This does not really work well with min-even parity conditions
/// so this helper trait is introduced.
// TODO: remove this if possible.
pub trait ReducesTo<T = bool> {
    /// Reduce `self` to a value of type `T`.
    fn reduce(self) -> T;
}

impl ReducesTo<bool> for bool {
    fn reduce(self) -> bool {
        self
    }
}

impl ReducesTo<bool> for usize {
    fn reduce(self) -> bool {
        (self % 2) == 0
    }
}

impl ReducesTo<bool> for BTreeSet<bool> {
    fn reduce(self) -> bool {
        self.into_iter().any(|x| x)
    }
}

impl ReducesTo<bool> for BTreeSet<usize> {
    fn reduce(self) -> bool {
        self.into_iter().min().unwrap() % 2 == 0
    }
}
