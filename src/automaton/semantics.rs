use crate::prelude::*;

/// This trait is implemented by acceptance conditions for finite words.
/// See the module level documentation for details.
pub trait FiniteSemantics<Q, C> {
    /// The type of output that this semantic produces.
    type Output;
    /// Compute the output for the given finite run.
    fn finite_semantic<R>(&self, run: R) -> Self::Output
    where
        R: FiniteRun<StateColor = Q, EdgeColor = C>;
}

/// This trait is implemented by acceptance conditions for omega words.
/// See the module level documentation for more information.
pub trait OmegaSemantics<Q, C> {
    /// The type of output that this semantic produces.
    type Output;
    /// Compute the output for the given omega run.
    fn omega_semantic<R>(&self, run: R) -> Self::Output
    where
        R: OmegaRun<StateColor = Q, EdgeColor = C>;
}
