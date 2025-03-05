/// An alphabet defines a collection of possible symbols. This
/// module implements simple alphabets which consist of just a
/// collection of symbols, and propositional alphabets where each
/// symbol is represented by a boolean expression over some
/// set of base atomic propositions.
#[macro_use]
pub mod alphabet;

/// A word is a sequence of symbols from some alphabet. Herein,
/// different types of words are defined, specifically finite ones
/// and different reprsentations of infinite ones.
/// Moreover, some constructions of manipulating words, taking suffixes,
/// infixes and such are given.
/// Finally, the module also implements normalization for words.
#[macro_use]
pub mod word;

/// Defines some mathematical objects that are used such as bijections,
/// sets and mappings.
pub mod math;

mod show;
pub use show::Show;

/// Defines a representation of directed, acyclic graphs. These are for example
/// used for the representation of the strongly connected components of a transition system.
pub mod dag;

/// Alias for the default integer type that is used for coloring edges and states.
pub type Int = u8;

/// Represents the absence of a color. The idea is that this can be used when collecting
/// a transitions system as it can always be constructed from a color by simply forgetting it.
/// This is useful for example when we want to collect a transition system into a different
/// representation, but we don't care about the colors on the edges. In that case, the state
/// colors may be kept and the edge colors are dropped.
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct Void;

impl std::fmt::Debug for Void {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#")
    }
}

/// A color is simply a type that can be used to color states or transitions.
pub trait Color: Clone + Eq + std::hash::Hash + std::fmt::Debug {
    /// Reduces a sequence of colors (of type `Self`) to a single color of type `Self`.
    fn reduce<I: IntoIterator<Item = Self>>(iter: I) -> Self
    where
        Self: Sized + Ord,
    {
        iter.into_iter().min().unwrap()
    }
}

impl<T: Eq + Clone + std::hash::Hash + std::fmt::Debug> Color for T {}

/// Represents an ordered, finite set of colors.
pub trait Lattice {
    /// Gives an instance of the bottom, i.e. least possible color.
    fn bottom() -> Self;
    /// Gives an instance of the top, i.e. greatest possible color.
    fn top() -> Self;
    /// Joins the two colors, i.e. the least upper bound. Think of this
    /// as a union operation for sets and as maximum for numbers
    fn join(&self, other: &Self) -> Self;
    /// Joins the two colors in place. See [`Lattice::join`].
    fn join_assign(&mut self, other: &Self)
    where
        Self: Sized,
    {
        *self = self.join(other);
    }
    /// Computes the join of all colors in an iterator.
    fn join_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self
    where
        Self: 'a;
    /// Meets the two colors, i.e. the greatest lower bound. Think of this
    /// as a intersection operation for sets and as minimum for numbers
    fn meet(&self, other: &Self) -> Self;
    /// Meets the two colors in place. See [`Lattice::meet`].
    fn meet_assign(&mut self, other: &Self)
    where
        Self: Sized,
    {
        *self = self.meet(other);
    }
    /// Computes the meet of all colors in an iterator.
    fn meet_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self
    where
        Self: 'a;
}

impl Lattice for bool {
    fn bottom() -> Self {
        false
    }
    fn top() -> Self {
        true
    }
    fn join(&self, other: &Self) -> Self {
        *self || *other
    }
    fn meet(&self, other: &Self) -> Self {
        *self && *other
    }
    fn join_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self
    where
        Self: 'a,
    {
        iter.into_iter().any(|x| *x)
    }
    fn meet_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self
    where
        Self: 'a,
    {
        iter.into_iter().all(|x| *x)
    }
}

macro_rules! impl_with_limits {
    ($($ty:ident),*) => {
        $(
            impl Lattice for $ty {
                fn bottom() -> Self {  $ty::MIN }
                fn top() -> Self {  $ty::MAX }
                fn join(&self, other: &Self) -> Self {
                    std::cmp::max(*self, *other)
                }
                fn meet(&self, other: &Self) -> Self {
                    std::cmp::min(*self, *other)
                }
                fn join_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self where Self: 'a{
                    iter.into_iter().max().cloned().unwrap_or(Self::bottom())
                }
                fn meet_iter<'a>(iter: impl IntoIterator<Item = &'a Self>) -> Self where Self: 'a{
                    iter.into_iter().min().cloned().unwrap_or(Self::top())
                }
            }
        )*
    };
}

impl_with_limits!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);
