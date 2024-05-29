use crate::innerlude::*;

pub trait TransitionSystemBase {
    type Alphabet: Alphabet;
    type StateIndex: IdType;
    type StateColor: Color;
    type EdgeColor: Color;
}

impl<T: TransitionSystemBase> TransitionSystemBase for &T {
    type Alphabet = T::Alphabet;
    type EdgeColor = T::EdgeColor;
    type StateColor = T::StateColor;
    type StateIndex = T::StateIndex;
}

impl<T: TransitionSystemBase> TransitionSystemBase for &mut T {
    type Alphabet = T::Alphabet;
    type EdgeColor = T::EdgeColor;
    type StateColor = T::StateColor;
    type StateIndex = T::StateIndex;
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
}
