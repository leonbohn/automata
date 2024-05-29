use crate::innerlude::*;

mod base;
pub use base::TransitionSystemBase;

mod states;
pub use states::StateIterable;

/// Encapsulates what is necessary for a type to be usable as a state index in a [`TransitionSystem`].
pub trait IdType: Copy + std::hash::Hash + std::fmt::Debug + Eq + Ord + Show {}
impl<TY: Copy + std::hash::Hash + std::fmt::Debug + Eq + Ord + Show> IdType for TY {}

/// Helper trait for extracting the [`crate::alphabet::Symbol`] type from an a transition system.
pub type Symbol<A = base::DefaultBase> =
    <<A as TransitionSystemBase>::Alphabet as Alphabet>::Symbol;
/// Helper trait for extracting the [`Expression`] type from an a transition system.
pub type Expression<A = base::DefaultBase> =
    <<A as TransitionSystemBase>::Alphabet as Alphabet>::Expression;
/// Type alias for extracting the state color in a [`TransitionSystem`].
pub type StateColor<X = base::DefaultBase> = <X as TransitionSystemBase>::StateColor;
/// Type alias for extracting the edge color in a [`TransitionSystem`].
pub type EdgeColor<X = base::DefaultBase> = <X as TransitionSystemBase>::EdgeColor;
/// Type alias for extracting the state index in a [`TransitionSystem`].
pub type StateIndex<X = base::DefaultBase> = <X as TransitionSystemBase>::StateIndex;

/// Marker trait for [`IdType`]s that are scalar, i.e. they can be converted to and from `usize`.
pub trait ScalarIdType:
    IdType + std::ops::Add<Output = Self> + std::ops::Sub<Output = Self>
{
    /// Converts a `usize` to the implementing type.
    fn from_usize(n: usize) -> Self;
    /// Converts the implementing type to a `usize`.
    fn into_usize(self) -> usize;
}
impl ScalarIdType for usize {
    fn from_usize(n: usize) -> Self {
        n
    }
    fn into_usize(self) -> usize {
        self
    }
}
impl ScalarIdType for u32 {
    fn from_usize(n: usize) -> Self {
        n as u32
    }
    fn into_usize(self) -> usize {
        self as usize
    }
}
