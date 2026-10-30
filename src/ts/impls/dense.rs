use crate::{
    Void,
    alphabet::{CharAlphabet, IndexedAlphabet},
    ts::{DefaultIdType, EdgeId},
};

/// The sentinel that stands for "no edge" in the target slots of [`DenseTs`].
pub(super) const NONE: DefaultIdType = DefaultIdType::MAX;

/// A deterministic transition system over an [`IndexedAlphabet`] that stores the transitions in a
/// table with one slot per state and symbol.
///
/// # Layout
/// For `n` states and an alphabet of size `k`, the edge leaving state `q` on the symbol with
/// index `a` lives in slot `q * k + a`, which is also its [`EdgeId`]. Looking up an edge is thus one
/// index computation and a load. The targets and colors of the slots are kept in two separate
/// vectors, a target of [`NONE`] marks an absent edge.
///
/// No expression is stored per edge, it is recovered from the alphabet via
/// [`IndexedAlphabet::expression_from_index`].
///
/// Every state keeps a list of its incoming [`EdgeId`]s so that predecessors are available.
///
/// A removed state is a tombstone (`None` in `states`), so that the indices of all other states stay
/// valid.
#[derive(Clone)]
pub struct DenseTs<A: IndexedAlphabet = CharAlphabet, Q = Void, C = Void> {
    alphabet: A,
    states: Vec<Option<Q>>,
    targets: Vec<DefaultIdType>,
    colors: Vec<Option<C>>,
    predecessors: Vec<Vec<EdgeId>>,
}
