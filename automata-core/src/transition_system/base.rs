use crate::innerlude::*;

pub trait TransitionSystemBase {
    type Alphabet: Alphabet;
    type StateIndex: IdType;
    type StateColor: Color;
    type EdgeColor: Color;

    fn alphabet(&self) -> &Self::Alphabet;
}

impl<T: TransitionSystemBase> TransitionSystemBase for &T {
    type Alphabet = T::Alphabet;
    type EdgeColor = T::EdgeColor;
    type StateColor = T::StateColor;
    type StateIndex = T::StateIndex;

    fn alphabet(&self) -> &Self::Alphabet {
        T::alphabet(self)
    }
}

impl<T: TransitionSystemBase> TransitionSystemBase for &mut T {
    type Alphabet = T::Alphabet;
    type EdgeColor = T::EdgeColor;
    type StateColor = T::StateColor;
    type StateIndex = T::StateIndex;

    fn alphabet(&self) -> &Self::Alphabet {
        T::alphabet(self)
    }
}

pub(crate) struct DefaultBase<
    A: Alphabet = CharAlphabet,
    Q: Color = Void,
    C: Color = Void,
    Idx: IdType = DefaultIdType,
>(std::marker::PhantomData<(A, Q, C, Idx)>);
impl<A: Alphabet, Q: Color, C: Color, Idx: IdType> TransitionSystemBase
    for DefaultBase<A, Q, C, Idx>
{
    type Alphabet = A;
    type EdgeColor = C;
    type StateColor = Q;
    type StateIndex = Idx;
    fn alphabet(&self) -> &Self::Alphabet {
        panic!("This impl only provides types!")
    }
}
