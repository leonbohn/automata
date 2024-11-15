mod flat {

    #[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Copy)]
    pub struct Position(u32);

    impl From<usize> for Position {
        fn from(value: usize) -> Self {
            Self(value.try_into().expect("cannot convert usize to position"))
        }
    }
    impl From<Position> for usize {
        fn from(value: Position) -> Self {
            value.0 as usize
        }
    }
    impl std::ops::Deref for Position {
        type Target = u32;
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }
    impl std::ops::DerefMut for Position {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    #[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
    pub enum Fragment {
        Not(Position),
        Or(Position, Position),
        ManyOr(Vec<Position>),
        And(Position, Position),
        ManyAnd(Vec<Position>),
        Xor(Position, Position),
        True,
        False,
        Boolean(bool),
        APName(String),
    }

    impl Fragment {
        fn r#true() -> Self {
            Self::True
        }
        fn r#false() -> Self {
            Self::False
        }
        fn boolean(b: bool) -> Self {
            Self::Boolean(b)
        }
    }

    pub struct LTLFormula {
        fragments: Vec<Fragment>,
        root: Position,
    }

    impl LTLFormula {
        pub fn r#true() -> Self {
            Self::singleton(Fragment::r#true())
        }

        pub fn r#false() -> Self {
            Self::singleton(Fragment::r#false())
        }

        pub fn boolean(b: bool) -> Self {
            Self::singleton(Fragment::boolean(b))
        }

        pub fn singleton(fragment: Fragment) -> Self {
            Self::new(vec![fragment], 0.into())
        }

        pub fn and(self, other: LTLFormula) -> Self {
            // self.fragments.extend(other.fragments);
            let _new_id = self.fragments.len();
            todo!()
        }

        pub fn ap(name: String) -> Self {
            Self::singleton(Fragment::APName(name))
        }

        pub fn new(fragments: Vec<Fragment>, root: Position) -> Self {
            Self { fragments, root }
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Copy)]
pub struct APIndex(u8);

impl From<usize> for APIndex {
    fn from(value: usize) -> Self {
        Self(value.try_into().expect("cannot convert usize to position"))
    }
}
impl From<APIndex> for usize {
    fn from(value: APIndex) -> Self {
        value.0 as usize
    }
}
impl std::ops::Deref for APIndex {
    type Target = u8;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for APIndex {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum LTL {
    True,
    False,
    AP(APIndex),
    ManyOr(Vec<LTL>),
    ManyAnd(Vec<LTL>),
    Not(Box<LTL>),
    G(Box<LTL>),
    F(Box<LTL>),
    U(Box<LTL>, Box<LTL>),
    X(Box<LTL>),
}

impl LTL {
    fn and(self, other: LTL) -> Self {
        match (self, other) {
            (LTL::True, o) => o,
            (LTL::False, _) => LTL::False,
            (s, LTL::True) => s,
            (_, LTL::False) => LTL::False,
            (LTL::ManyAnd(mut v1), LTL::ManyAnd(v2)) => {
                v1.extend(v2);
                LTL::ManyAnd(v1)
            }
            (LTL::ManyAnd(mut v1), o) => {
                v1.push(o);
                LTL::ManyAnd(v1)
            }
            (s, LTL::ManyAnd(mut v2)) => {
                v2.push(s);
                LTL::ManyAnd(v2)
            }
            (s, o) => LTL::ManyAnd(vec![s, o]),
        }
    }
    fn or(self, other: LTL) -> Self {
        match (self, other) {
            (LTL::True, _) => LTL::True,
            (LTL::False, o) => o,
            (_, LTL::True) => LTL::True,
            (s, LTL::False) => s,
            (LTL::ManyOr(mut v1), LTL::ManyOr(v2)) => {
                v1.extend(v2);
                LTL::ManyOr(v1)
            }
            (LTL::ManyOr(mut v1), o) => {
                v1.push(o);
                LTL::ManyOr(v1)
            }
            (s, LTL::ManyOr(mut v2)) => {
                v2.push(s);
                LTL::ManyOr(v2)
            }
            (s, o) => LTL::ManyOr(vec![s, o]),
        }
    }
    fn not(self) -> Self {
        match self {
            LTL::Not(f) => *f,
            LTL::True => LTL::False,
            LTL::False => LTL::True,
            _ => LTL::Not(self.into()),
        }
    }
    fn g(self) -> Self {
        if matches!(self, LTL::G(_)) {
            return self;
        }
        LTL::G(self.into())
    }
    fn f(self) -> Self {
        if matches!(self, LTL::F(_)) {
            return self;
        }
        LTL::F(self.into())
    }
    fn u(self, other: LTL) -> Self {
        LTL::U(self.into(), other.into())
    }
    fn x(self) -> Self {
        LTL::X(self.into())
    }
    fn top() -> Self {
        Self::True
    }
    fn bot() -> Self {
        Self::False
    }
    fn boolean(b: bool) -> Self {
        if b {
            Self::True
        } else {
            Self::False
        }
    }
}
