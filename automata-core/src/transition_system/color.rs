pub trait Gives<X> {
    fn give_ref(&self) -> &X;
    fn give_owned(self) -> X;
    fn give_cloned(&self) -> X;
}

pub enum Weak<'a, X> {
    Borrowed(&'a X),
    Owneded(X),
}
use std::borrow::Borrow;

use Weak::*;

impl<'a, X> std::ops::Deref for Weak<'a, X> {
    type Target = X;
    fn deref(&self) -> &Self::Target {
        match self {
            Borrowed(x) => x,
            Owneded(x) => x,
        }
    }
}

impl<'a, X> std::borrow::Borrow<X> for Weak<'a, X> {
    fn borrow(&self) -> &X {
        std::ops::Deref::deref(self)
    }
}

impl<'a, X: Clone> Gives<X> for Weak<'a, X> {
    fn give_ref(&self) -> &X {
        self.borrow()
    }

    fn give_owned(self) -> X {
        match self {
            Borrowed(x) => x.clone(),
            Owneded(x) => x,
        }
    }

    fn give_cloned(&self) -> X {
        match self {
            Borrowed(x) => (*x).clone(),
            Owneded(x) => x.clone(),
        }
    }
}

impl<X: Clone> Gives<X> for X {
    fn give_ref(&self) -> &X {
        self
    }
    fn give_owned(self) -> X {
        self
    }
    fn give_cloned(&self) -> X {
        self.clone()
    }
}
impl<X: Clone> Gives<X> for &X {
    fn give_ref(&self) -> &X {
        self
    }
    fn give_owned(self) -> X {
        self.clone()
    }
    fn give_cloned(&self) -> X {
        (*self).clone()
    }
}
