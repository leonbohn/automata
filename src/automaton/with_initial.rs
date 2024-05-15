use crate::prelude::*;
use std::fmt::Debug;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct NoSemantics;
pub type WithInitial<Ts> = Automaton<Ts, NoSemantics>;
