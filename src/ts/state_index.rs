/// Encapsulates what is necessary for a type to be usable as a state index in a [`crate::TransitionSystem`].
pub trait IndexType: Copy + std::hash::Hash + std::fmt::Debug + Eq + Ord {}
impl<T: Copy + std::hash::Hash + std::fmt::Debug + Eq + Ord> IndexType for T {}

/// Marker trait for [`IndexType`]s that are scalar, i.e. they can be converted to and from `usize`.
pub trait ScalarIndexType:
    IndexType + std::ops::Add<Output = Self> + std::ops::Sub<Output = Self>
{
    /// Converts a `usize` to the implementing type.
    fn from_usize(n: usize) -> Self;
    /// Converts the implementing type to a `usize`.
    fn into_usize(self) -> usize;
    /// Casts `self` into a [`ScalarIndexType`] of a different type.
    fn into_index<T: ScalarIndexType>(self) -> T {
        T::from_usize(self.into_usize())
    }
    /// Converts an index of a [`petgraph::stable_graph::StableGraph`] into an instance of the
    /// implementing type.
    #[cfg(feature = "petgraph")]
    fn from_pg_index(n: petgraph::stable_graph::NodeIndex<Self>) -> Self
    where
        Self: petgraph::stable_graph::IndexType,
    {
        Self::from_usize(n.index())
    }
    /// Converts `self` into a [`petgraph::stable_graph::NodeIndex`] which can be used to access
    /// a node in a [`petgraph::stable_graph::StableGraph`].
    #[cfg(feature = "petgraph")]
    fn into_pg_index(self) -> petgraph::stable_graph::NodeIndex<Self>
    where
        Self: petgraph::stable_graph::IndexType,
    {
        petgraph::stable_graph::NodeIndex::new(self.into_usize())
    }
}

macro_rules! int_index_type {
    ($($t:ty),*) => {
        $(
            impl ScalarIndexType for $t {
                fn from_usize(from: usize) -> Self {
                    from as $t
                }
                fn into_usize(self) -> usize {
                    self as usize
                }
            }
        )*
    };
}

int_index_type!(usize, u8, u16, u32);
