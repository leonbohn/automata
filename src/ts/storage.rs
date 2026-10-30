use crate::Color;
use crate::alphabet::{Alphabet, IndexedAlphabet};
use crate::ts::{CsrTs, DenseTs, Det, ForAlphabet, LinkedTs, Sproutable, States};

/// A family of representations for owned, growable transition systems. A storage is a marker that
/// is chosen at the type level and turned into a concrete system by [`Storage::Ts`], which fixes
/// the colors. This allows code to be generic over the representation without naming a concrete
/// system, for example a parser that is instantiated with [`Linked`] or with [`Det<Linked>`].
/// Whether a system can be grown is not part of this, see [`SproutableStorage`].
///
/// Only systems that own their states and edges have a storage. Lazy views (products, recolorings,
/// subset constructions) do not.
///
/// [`Det<Linked>`]: crate::ts::Det
pub trait Storage<A: Alphabet> {
    /// Whether the systems of this storage are deterministic, that is whether adding an edge
    /// replaces the edges that overlap with it. The builder uses this to report overlapping edges
    /// instead of silently dropping them.
    const DETERMINISTIC: bool;

    /// The transition system of this storage with the given colors.
    type Ts<Q: Color, C: Color>: States<Alphabet = A, StateColor = Q, EdgeColor = C>;

    /// Converts a non-deterministic [`LinkedTs`] into this storage. A storage that cannot
    /// represent `ts` (because it is deterministic and `ts` is not) returns it as the error.
    fn try_from_linked<Q: Color, C: Color>(
        ts: LinkedTs<A, Q, C>,
    ) -> Result<Self::Ts<Q, C>, LinkedTs<A, Q, C>>;
}

/// A [`Storage`] whose systems can be grown state by state and edge by edge, which is what the
/// builder and the parsers need. Storages that are built in one go from another system (like
/// [`Csr`]) only implement [`Storage`].
pub trait SproutableStorage<A: Alphabet>: Storage<A> {
    /// The system of this storage that can be grown, a type that converts into [`Storage::Ts`]
    /// (for most storages it is the same type).
    type Grown<Q: Color, C: Color>: Sproutable<Alphabet = A, StateColor = Q, EdgeColor = C>
        + ForAlphabet<A>
        + Into<Self::Ts<Q, C>>;
}

/// The storage [`LinkedTs`]: non-deterministic, works for any alphabet.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Linked;

impl<A: Alphabet> SproutableStorage<A> for Linked {
    type Grown<Q: Color, C: Color> = LinkedTs<A, Q, C>;
}

impl<A: Alphabet> Storage<A> for Linked {
    const DETERMINISTIC: bool = false;

    type Ts<Q: Color, C: Color> = LinkedTs<A, Q, C>;

    fn try_from_linked<Q: Color, C: Color>(
        ts: LinkedTs<A, Q, C>,
    ) -> Result<Self::Ts<Q, C>, LinkedTs<A, Q, C>> {
        Ok(ts)
    }
}

/// The storage [`DenseTs`]: deterministic, works for [`IndexedAlphabet`]s and looks up edges in
/// constant time.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Dense;

impl<A: IndexedAlphabet> SproutableStorage<A> for Dense {
    type Grown<Q: Color, C: Color> = DenseTs<A, Q, C>;
}

impl<A: IndexedAlphabet> Storage<A> for Dense {
    const DETERMINISTIC: bool = true;

    type Ts<Q: Color, C: Color> = DenseTs<A, Q, C>;

    fn try_from_linked<Q: Color, C: Color>(
        ts: LinkedTs<A, Q, C>,
    ) -> Result<Self::Ts<Q, C>, LinkedTs<A, Q, C>> {
        if ts.is_deterministic() {
            Ok(DenseTs::sprout_from_ts(ts))
        } else {
            Err(ts)
        }
    }
}

/// The storage [`CsrTs`]: deterministic, works for [`IndexedAlphabet`]s, looks up edges in constant
/// time and cannot be changed once built, see [`SproutableStorage`] for the ones that can.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Csr;

impl<A: IndexedAlphabet> Storage<A> for Csr {
    const DETERMINISTIC: bool = true;

    type Ts<Q: Color, C: Color> = CsrTs<A, Q, C>;

    fn try_from_linked<Q: Color, C: Color>(
        ts: LinkedTs<A, Q, C>,
    ) -> Result<Self::Ts<Q, C>, LinkedTs<A, Q, C>> {
        Det::try_new(ts).map(|ts| CsrTs::from_ts(&ts))
    }
}
