use std::{fmt::Debug, hash::Hash};

pub mod math;

mod show;
pub use show::Show;

pub mod alphabet;

pub mod transition_system;
pub use transition_system::{IdType, ScalarIdType};

pub type DefaultIdType = u32;

/// A color is simply a type that can be used to color states or transitions.
pub trait Color: Clone + Eq + Hash + Debug {
    /// Reduces a sequence of colors (of type `Self`) to a single color of type `Self`.
    fn reduce<I: IntoIterator<Item = Self>>(iter: I) -> Self
    where
        Self: Sized + Ord,
    {
        iter.into_iter().min().unwrap()
    }
}

impl<T: Eq + Clone + Hash + Debug> Color for T {}

/// Alias for the default integer type that is used for coloring edges and states.
pub type Int = u8;

/// Represents the absence of a color. The idea is that this can be used when collecting
/// a transitions system as it can always be constructed from a color by simply forgetting it.
/// This is useful for example when we want to collect a transition system into a different
/// representation, but we don't care about the colors on the edges. In that case, the state
/// colors may be kept and the edge colors are dropped.
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct Void;

impl Debug for Void {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#")
    }
}

pub(crate) mod innerlude {
    pub use super::{
        alphabet::{Alphabet, AlphabetExpression, AlphabetSymbol, CharAlphabet, Matcher},
        transition_system::{
            EdgeColor, Expression, StateColor, StateIndex, StateIterable, Symbol,
            TransitionSystemBase,
        },
        Color, DefaultIdType, IdType, Int, Show, Void,
    };
}
