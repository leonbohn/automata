/// Encapsulates what is necessary for a type to be usable as a state id in a
/// [`crate::TransitionSystem`].
///
/// Ids are generic, so that lazy and implicit systems keep their natural ids (e.g. a pair for a
/// product or a set of states for a subset construction). Ids that are (or can cheaply be mapped
/// to) a small integer should additionally implement [`DenseId`] and override [`Self::to_dense`]
/// and [`Self::from_dense`], which allows algorithms to use bitsets and vectors instead of hash
/// based containers, see [`crate::ts::StateSet`] and [`crate::ts::StateMap`].
pub trait IdType: Copy + std::hash::Hash + std::fmt::Debug + Eq + Ord {
    /// Returns the dense representation of `self`, if the type has one. Types that implement
    /// [`DenseId`] must return `Some`, all others return `None` (the default).
    #[inline(always)]
    fn to_dense(self) -> Option<usize> {
        None
    }
    /// Inverse of [`Self::to_dense`].
    #[inline(always)]
    fn from_dense(_n: usize) -> Option<Self> {
        None
    }
}

/// An [`IdType`] that can be converted to and from `usize`. Ids of this type are expected to be
/// assigned (mostly) contiguously from `0`, so that they can be used to index into vectors and
/// bitsets.
pub trait DenseId: IdType {
    /// Converts a `usize` to the implementing type.
    ///
    /// # Panics
    /// May panic or truncate if `n` is out of range for the type.
    fn from_usize(n: usize) -> Self;
    /// Converts the implementing type to a `usize`.
    fn into_usize(self) -> usize;
    /// Casts `self` into a [`DenseId`] of a different type.
    fn into_id<T: DenseId>(self) -> T {
        T::from_usize(self.into_usize())
    }
}

macro_rules! int_id_type {
    ($($t:ty),*) => {
        $(
            impl IdType for $t {
                #[inline(always)]
                fn to_dense(self) -> Option<usize> {
                    Some(self as usize)
                }
                #[inline(always)]
                fn from_dense(n: usize) -> Option<Self> {
                    <$t>::try_from(n).ok()
                }
            }
            impl DenseId for $t {
                #[inline(always)]
                fn from_usize(from: usize) -> Self {
                    from as $t
                }
                #[inline(always)]
                fn into_usize(self) -> usize {
                    self as usize
                }
            }
        )*
    };
}

int_id_type!(usize, u8, u16, u32);

/// Identifies an edge of a transition system. This is a newtype so that edge ids cannot be mixed
/// up with state ids.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct EdgeId(pub u32);

impl IdType for EdgeId {
    #[inline(always)]
    fn to_dense(self) -> Option<usize> {
        Some(self.0 as usize)
    }
    #[inline(always)]
    fn from_dense(n: usize) -> Option<Self> {
        u32::try_from(n).ok().map(EdgeId)
    }
}
impl DenseId for EdgeId {
    #[inline(always)]
    fn from_usize(n: usize) -> Self {
        EdgeId(n as u32)
    }
    #[inline(always)]
    fn into_usize(self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for EdgeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "e{}", self.0)
    }
}
