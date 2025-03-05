use crate::TransitionSystem;
use crate::automaton::Automaton;
use crate::ts::{EdgeColor, StateColor};
use std::fmt::Debug;

/// Auxiliary type that is used as marker for an [`Automaton`] where we are not
/// interested in the semantics.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct WithoutCondition;

/// An [`Automaton`] which has no semantics. Essentially, this just fixes one
/// state as initial.
pub type WithInitial<T> =
    Automaton<<T as TransitionSystem>::Alphabet, WithoutCondition, StateColor<T>, EdgeColor<T>, T>;

impl<Ts: TransitionSystem> WithInitial<Ts> {
    /// Decompose `self` into the transition system and the initial state. This operation
    /// naturally takes ownership of `self` and disregards the semantics (which should not
    /// matter as it should be [`WithoutCondition`] anyways).
    pub fn decompose(self) -> (Ts, Ts::StateIndex) {
        (self.ts, self.initial)
    }
}
