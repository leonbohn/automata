use std::{fmt::Debug, hash::Hash};

pub mod math;

mod show;
pub use show::Show;

pub mod alphabet;

pub mod transition_system;
pub use transition_system::{IdType, ScalarIdType};

pub type DefaultIdType = u32;

pub trait Knows<X> {
    fn point(&self) -> &X;
    fn clone(&self) -> X;
    fn give(self) -> X;
}

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
    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
    pub type TS<A = CharAlphabet, Q = Void, C = Void, const DET: bool = true> =
        GraphTs<A, Q, C, DET>;
    /// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
    pub type DTS<A = CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, true>;
    /// Points to the default implementation of [`TransitionSystem`] in the case where it is
    /// **now known to be** [`Deterministic`].
    pub type NTS<A = CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, false>;

    pub use super::{
        alphabet,
        alphabet::{Alphabet, AlphabetExpression, AlphabetSymbol, CharAlphabet, Matcher},
        math,
        transition_system::{
            EdgeColor, EdgeReference, EdgeTuple, Edges, EdgesFrom, Expression, ForAlphabet, Gives,
            GraphTs, IntoEdgeTuple, PredecessorIterable, ScalarIdType, Shrinkable, Sproutable,
            StateColor, StateIndex, StateIterable, StateReference, States, Symbol, TSBuilder,
            TransitionSystemBase, Weak,
        },
        Color, DefaultIdType, IdType, Int, Knows, Show, Void,
    };
}
