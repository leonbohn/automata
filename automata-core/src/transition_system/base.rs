use crate::{Color, IdType};

pub trait TransitionSystemBase {
    type StateIndex: IdType;
    type StateColor: Color;
    type EdgeColor: Color;
}
