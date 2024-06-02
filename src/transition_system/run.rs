use crate::prelude::*;
/// A run is a sequence of states and edges that is consistent with the transition system.
/// Implementors of this trait represent such a run.
pub trait FiniteRun {
    /// The type of the state colors.
    type StateColor;
    /// The type of the edge colors.
    type EdgeColor;
    /// The type of the state indices.
    type StateIndex: IdType;
    /// Returns an iterator over the state colors.
    fn state_colors(self) -> Option<impl Iterator<Item = Self::StateColor>>;
    /// Returns an iterator over the edge colors.
    fn edge_colors(self) -> Option<impl Iterator<Item = Self::EdgeColor>>;
    /// Returns an iterator over the state indices.
    fn indices(self) -> Option<impl Iterator<Item = Self::StateIndex>>;
    /// Returns whether the run is successful.
    fn successful(&self) -> bool;
}

impl<A: Alphabet, Q: Clone, C: Clone, Idx: IdType> FiniteRun
    for super::deterministic::FiniteRunResult<A, Idx, Q, C>
{
    type StateColor = Q;
    type EdgeColor = C;
    type StateIndex = Idx;

    fn state_colors(self) -> Option<impl Iterator<Item = Self::StateColor>> {
        self.ok().map(|run| run.into_state_colors())
    }

    fn edge_colors(self) -> Option<impl Iterator<Item = Self::EdgeColor>> {
        self.ok().map(|run| run.into_edge_colors())
    }

    fn indices(self) -> Option<impl Iterator<Item = Self::StateIndex>> {
        self.ok().map(|run| run.into_state_sequence())
    }

    fn successful(&self) -> bool {
        self.is_ok()
    }
}

/// A run is a sequence of states and edges that is consistent with the transition system.
/// Implementors of this trait represent an infinite run.
pub trait OmegaRun {
    /// The type of the state colors.
    type StateColor;
    /// The type of the edge colors.
    type EdgeColor;
    /// The type of the state indices.
    type StateIndex: IdType;
    /// Returns an iterator over the state colors.
    fn recurring_state_colors_iter(self) -> Option<impl Iterator<Item = Self::StateColor>>;
    /// Returns an iterator over the edge colors.
    fn recurring_edge_colors_iter(self) -> Option<impl Iterator<Item = Self::EdgeColor>>;
    /// Returns an iterator over the state indices.
    fn recurring_state_indices_iter(self) -> Option<impl Iterator<Item = Self::StateIndex>>;
}

impl<A: Alphabet, Q: Clone, C: Clone, Idx: IdType> OmegaRun
    for super::deterministic::OmegaRunResult<A, Idx, Q, C>
{
    type StateColor = Q;

    type EdgeColor = C;

    type StateIndex = Idx;

    fn recurring_state_colors_iter(self) -> Option<impl Iterator<Item = Self::StateColor>> {
        self.ok().map(|path| path.into_recurrent_state_colors())
    }

    fn recurring_edge_colors_iter(self) -> Option<impl Iterator<Item = Self::EdgeColor>> {
        self.ok().map(|path| path.into_recurrent_edge_colors())
    }

    fn recurring_state_indices_iter(self) -> Option<impl Iterator<Item = Self::StateIndex>> {
        self.ok().map(|path| path.into_recurrent_state_indices())
    }
}
