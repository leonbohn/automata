/// Encapsulates what is necessary for a type to be usable as a state index in a [`TransitionSystem`].
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

int_index_type!(usize, u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);
