use std::{
    fmt::Debug,
    hash::Hash,
    ops::{Deref, DerefMut},
};

pub trait IdType: Copy + Eq + Hash + Ord + Debug {}

macro_rules! impl_integer_id_type {
    ($($t:ty),*) => {
        $(
            impl IdType for $t {}
        )*
    }
}

impl_integer_id_type!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

pub type DefaultIdType = u32;

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct Id<N: IdType = DefaultIdType>(pub N);

impl<N: IdType + Debug> Debug for Id<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "q{:?}", self.0)
    }
}

impl<N: RepresentableId> From<usize> for Id<N> {
    fn from(n: usize) -> Self {
        Id(N::from_representation(n))
    }
}

impl<N: IdType> DerefMut for Id<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<N: IdType> Deref for Id<N> {
    type Target = N;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<N: IdType> AsRef<N> for Id<N> {
    fn as_ref(&self) -> &N {
        &self.0
    }
}

impl<N: IdType> Id<N> {
    pub fn inner(self) -> N {
        self.0
    }
    pub fn from_usize(n: usize) -> Self
    where
        N: RepresentableId,
    {
        Self(N::from_representation(n))
    }
    pub fn into_usize(self) -> usize
    where
        N: RepresentableId,
    {
        self.inner().into_representation()
    }
}

pub trait IntoId<N: IdType> {
    fn into_id(self) -> Id<N>;
}

macro_rules! impl_integer_into_id {
    ($($t:ty),*) => {
        $(
            impl IntoId<DefaultIdType> for $t {
                fn into_id(self) -> Id<DefaultIdType> {
                    Id(self as DefaultIdType)
                }
            }
        )*
    }
}

impl_integer_into_id!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

pub trait FromId<N: IdType> {
    fn from_id(id: Id<N>) -> Self;
}

macro_rules! impl_integer_from_id {
    ($($t:ty),*) => {
        $(
            impl FromId<DefaultIdType> for $t {
                fn from_id(id: Id<DefaultIdType>) -> Self {
                    id.0 as $t
                }
            }
        )*
    }
}

impl_integer_from_id!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

pub trait RepresentableId: IdType + Ord + Eq + 'static + Debug {
    fn from_representation(n: usize) -> Self;
    fn into_representation(self) -> usize;
}

macro_rules! impl_integer_representable_id {
    ($($t:ty),*) => {
        $(
            impl RepresentableId for $t {
                fn from_representation(n: usize) -> Self {
                    n as $t
                }
                fn into_representation(self) -> usize {
                    self as usize
                }
            }
        )*
    }
}

impl_integer_representable_id!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
