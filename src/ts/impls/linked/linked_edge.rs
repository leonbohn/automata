use crate::ts::{DefaultIdType, EdgeRef};
use std::fmt::Debug;

/// The sentinel that stands for "no edge" in the list links of the linked storage and for "no state"
/// in the endpoints of a removed edge.
pub(super) const NONE: u32 = u32::MAX;

/// An edge of the linked storage. The four links and the two endpoints are `u32`s with [`NONE`] as
/// the sentinel, which is 24 bytes of bookkeeping per edge.
///
/// A removed edge stays in the edge vector as a tombstone (`source == NONE`) so that the ids of all
/// other edges stay valid. A tombstone is not part of any list.
#[derive(Clone, Eq, PartialEq, Hash)]
#[repr(align(8))]
pub(super) struct LinkedEdge<E, C> {
    pub(super) source: u32,
    pub(super) target: u32,
    pub(super) out_prev: u32,
    pub(super) out_next: u32,
    pub(super) in_prev: u32,
    pub(super) in_next: u32,
    pub(super) expression: E,
    pub(super) color: C,
}

impl<E, C> LinkedEdge<E, C> {
    /// Creates an edge that is not linked into any list yet.
    pub(super) fn new(source: u32, expression: E, color: C, target: u32) -> Self {
        Self {
            source,
            target,
            out_prev: NONE,
            out_next: NONE,
            in_prev: NONE,
            in_next: NONE,
            expression,
            color,
        }
    }

    #[inline(always)]
    pub(super) fn is_live(&self) -> bool {
        self.source != NONE
    }

    /// Turns the edge into a tombstone. The expression and color stay in place until the storage is
    /// compacted.
    pub(super) fn tombstone(&mut self) {
        self.source = NONE;
        self.target = NONE;
        self.out_prev = NONE;
        self.out_next = NONE;
        self.in_prev = NONE;
        self.in_next = NONE;
    }

    /// Replaces expression and color, keeping the endpoints and links.
    pub(super) fn map<EE, CC>(
        self,
        f: impl FnOnce(u32, E, C, u32) -> (EE, CC),
    ) -> LinkedEdge<EE, CC> {
        let (expression, color) = f(self.source, self.expression, self.color, self.target);
        LinkedEdge {
            source: self.source,
            target: self.target,
            out_prev: self.out_prev,
            out_next: self.out_next,
            in_prev: self.in_prev,
            in_next: self.in_next,
            expression,
            color,
        }
    }
}

impl<E, C: Clone> LinkedEdge<E, C> {
    /// Returns the edge as the reference that transition systems yield.
    #[inline(always)]
    pub(super) fn as_edge_ref(&self) -> EdgeRef<'_, DefaultIdType, E, C> {
        EdgeRef::borrowed(self.source, &self.expression, &self.color, self.target)
    }
}

impl<E: Debug, C: Debug> Debug for LinkedEdge<E, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.is_live() {
            return write!(f, "LinkedEdge {{ removed }}");
        }
        let show = |x: u32| if x == NONE { -1 } else { x as i64 };
        write!(
            f,
            "LinkedEdge {{ {} --{:?}|{:?}--> {}   out[{}|{}], in[{}|{}] }}",
            self.source,
            self.expression,
            self.color,
            self.target,
            show(self.out_prev),
            show(self.out_next),
            show(self.in_prev),
            show(self.in_next),
        )
    }
}
