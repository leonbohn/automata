use crate::innerlude::*;

pub trait TransitionSystemBase {
    type Alphabet: Alphabet;

    fn alphabet(&self) -> &Self::Alphabet;
}

impl<T: TransitionSystemBase> TransitionSystemBase for &T {
    type Alphabet = T::Alphabet;
    fn alphabet(&self) -> &Self::Alphabet {
        T::alphabet(self)
    }
}

impl<T: TransitionSystemBase> TransitionSystemBase for &mut T {
    type Alphabet = T::Alphabet;
    fn alphabet(&self) -> &Self::Alphabet {
        T::alphabet(self)
    }
}

pub struct DefaultBase<
    A: Alphabet = CharAlphabet,
    Q: Color = Void,
    C: Color = Void,
    Idx: IdType = DefaultIdType,
>(std::marker::PhantomData<(A, Q, C, Idx)>);
impl<A: Alphabet, Q: Color, C: Color, Idx: IdType> TransitionSystemBase
    for DefaultBase<A, Q, C, Idx>
{
    type Alphabet = A;
    fn alphabet(&self) -> &Self::Alphabet {
        panic!("This impl only provides types!")
    }
}
