use std::ops::{Deref, DerefMut};

use super::{SimpleAlphabet, FDFA};

#[derive(Debug, Clone)]
pub struct SyntacticFDFA<A: SimpleAlphabet>(FDFA<A>);

impl<A: SimpleAlphabet> DerefMut for SyntacticFDFA<A> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<A: SimpleAlphabet> Deref for SyntacticFDFA<A> {
    type Target = FDFA<A>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
