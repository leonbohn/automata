use std::{
    hash::Hash,
    ops::{Deref, DerefMut},
};

pub trait IdType: Copy + Eq + Hash {}

macro_rules! impl_integer_id_type {
    ($($t:ty),*) => {
        $(
            impl IdType for $t {}
        )*
    }
}

impl_integer_id_type!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

pub type DefaultIdType = u32;

pub struct Id<N: IdType = DefaultIdType>(pub N);

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
