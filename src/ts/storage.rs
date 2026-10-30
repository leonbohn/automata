use crate::Color;
use crate::alphabet::{Alphabet, IndexedAlphabet};
use crate::ts::{DenseTs, ForAlphabet, LinkedTs, Sproutable, States};

/// A family of representations for owned, growable transition systems. A storage is a marker that
/// is chosen at the type level and turned into a concrete system by [`Storage::Ts`], which fixes
/// the colors. This allows code to be generic over the representation without naming a concrete
/// system, for example a parser that is instantiated with [`Linked`] or with [`Det<Linked>`].
///
/// Only systems that own their states and edges have a storage. Lazy views (products, recolorings,
/// subset constructions) do not.
///
/// [`Det<Linked>`]: crate::ts::Det
pub trait Storage<A: Alphabet> {
    /// The transition system of this storage with the given colors.
    type Ts<Q: Color, C: Color>: Sproutable<Alphabet = A, StateColor = Q, EdgeColor = C>
        + ForAlphabet<A>;

    /// Converts a non-deterministic [`LinkedTs`] into this storage. A storage that cannot
    /// represent `ts` (because it is deterministic and `ts` is not) returns it as the error.
    fn try_from_linked<Q: Color, C: Color>(
        ts: LinkedTs<A, Q, C>,
    ) -> Result<Self::Ts<Q, C>, LinkedTs<A, Q, C>>;
}

/// The storage [`LinkedTs`]: non-deterministic, works for any alphabet.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Linked;

impl<A: Alphabet> Storage<A> for Linked {
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

impl<A: IndexedAlphabet> Storage<A> for Dense {
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
