use std::{
    fmt::{Display, Write as _},
    hash::Hash,
    marker::PhantomData,
};

use itertools::Itertools;
use thiserror::Error;
use tracing::trace;

mod bdd;

use bdd::{Bdd, Cube};

use super::{Alphabet, CharAlphabet, Expression, Matcher};

/// Errors that can occur when building a [`PropAlphabet`] from another alphabet.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum PropAlphabetError {
    /// The number of symbols cannot be expressed as a number of atomic propositions.
    #[error(
        "an alphabet of size {0} cannot be represented by atomic propositions, the size must be a power of two and at least 2"
    )]
    InvalidSize(usize),
    /// A propositional alphabet needs at least one atomic proposition.
    #[error("a propositional alphabet needs at least one atomic proposition")]
    NoAtomicPropositions,
    /// More atomic propositions were requested than can be represented.
    #[error("{count} atomic propositions are too many, at most {max} are supported")]
    TooManyAtomicPropositions {
        /// The requested number of atomic propositions.
        count: usize,
        /// The maximum number of atomic propositions that is supported.
        max: usize,
    },
    /// An expression could not be parsed.
    #[error("invalid expression, unexpected input at position {position}")]
    InvalidExpression {
        /// The byte offset of the offending input.
        position: usize,
    },
    /// An expression mentions an atomic proposition that does not exist.
    #[error("the atomic proposition {ap} does not exist, there are only {num_aps}")]
    UnknownProposition {
        /// The index of the proposition.
        ap: usize,
        /// The number of atomic propositions.
        num_aps: u8,
    },
}

/// The integer type that stores a valuation of the atomic propositions as a bit vector: bit
/// `i` is set if the proposition with index `i` holds. Implemented for the unsigned integers.
pub trait RawSymbolRepr: std::fmt::Debug + Hash + Eq + Ord + Copy {
    /// Returns the stored bits as a `usize`.
    fn as_usize(&self) -> usize;
    /// Creates a value from the given bits.
    ///
    /// # Panics
    ///
    /// Panics if the value does not fit.
    fn from_usize(from: usize) -> Self;
    /// Returns true if the bit `n` (the proposition with index `n`) is set.
    fn bit(&self, n: usize) -> bool;
    /// Sets the bit `n`, i.e. makes the proposition with index `n` true.
    fn set(&mut self, n: usize);
    /// The maximum number of atomic propositions that can be stored.
    fn max_aps() -> usize;
}

macro_rules! impl_raw_symbol_repr {
    ($($ty:ty),*) => {
        $(
            impl RawSymbolRepr for $ty {
                fn max_aps() -> usize {
                    std::mem::size_of::<$ty>() * 8
                }
                fn as_usize(&self) -> usize {
                    *self as usize
                }
                fn from_usize(from: usize) -> Self {
                    from.try_into().unwrap()
                }
                fn bit(&self, n: usize) -> bool {
                    assert!(n <= Self::max_aps());
                    *self & (1 << n) != 0
                }
                fn set(&mut self, n: usize) {
                    assert!(n <= Self::max_aps());
                    *self |= 1 << n;
                }
            }
        )*
    }
}
impl_raw_symbol_repr!(u8, u16, u32, u64, u128, usize);

/// A symbol of a [`PropAlphabet`]: a valuation of its atomic propositions, i.e. a choice of
/// which of them are true.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct PropSymbol<RawTy: RawSymbolRepr = u32> {
    num_aps: u8,
    raw: RawTy,
}

impl<RawTy: RawSymbolRepr> PropSymbol<RawTy> {
    /// Turns the symbol into the expression that is satisfied by exactly this valuation.
    pub fn as_expression(&self) -> PropExpression<RawTy> {
        let repr = if self.num_aps > TABLE_APS {
            Repr::Bdd((0..self.num_aps).fold(Bdd::top(), |acc, ap| {
                let var = Bdd::var(ap);
                acc.and(&if self.raw.bit(raw_bit(self.num_aps, ap)) {
                    var
                } else {
                    var.not()
                })
            }))
        } else {
            Repr::Table(1 << self.raw.as_usize())
        };
        PropExpression {
            num_aps: self.num_aps,
            repr,
            _ty: PhantomData,
        }
    }
    /// Returns the letter `a`, `b`, ... that represents the valuation (its bits as a number).
    pub fn as_char(&self) -> char {
        (b'a' + ((self.raw.as_usize() as u8) & 0b1111)) as char
    }
    /// Creates a symbol over `aps` atomic propositions from a letter.
    ///
    /// # Panics
    ///
    /// Panics if `aps` is larger than the number of atomic propositions the representation supports,
    /// if `value` is not one of the letters `'a'` to `'o'`, or if `aps` does not fit into a `u8`.
    pub fn from_char(value: char, aps: usize) -> Self {
        assert!(aps <= RawTy::max_aps());
        let val = value as u8;
        assert!(b'a' <= val);
        assert!(val < b'p');

        Self {
            raw: RawTy::from_usize(((val - b'a') & 0b1111) as usize),
            num_aps: aps.try_into().unwrap(),
        }
    }
    /// Returns the valuation of the atomic propositions as a vector of booleans.
    ///
    /// # Panics
    ///
    /// Panics if the symbol has more atomic propositions than its representation can hold.
    pub fn as_bools(&self) -> Vec<bool> {
        assert!(
            self.num_aps as usize <= 8usize.saturating_pow(std::mem::size_of::<RawTy>() as u32)
        );

        let out = (0..self.num_aps).rev().fold(
            Vec::with_capacity(self.num_aps as usize),
            |mut acc, x| {
                acc.push(self.raw.bit(x as usize));
                acc
            },
        );
        trace!("got {out:?} from {self:?}");
        out
    }
    /// Creates a symbol from a valuation of the atomic propositions, the inverse of
    /// [`Self::as_bools`]: the first proposition is the most significant bit.
    ///
    /// # Panics
    ///
    /// Panics if there are more booleans than the representation can hold.
    pub fn from_bools(bools: Vec<bool>) -> Self {
        assert!(bools.len() <= 8usize.saturating_pow(std::mem::size_of::<RawTy>() as u32));
        let mut raw = RawTy::from_usize(0);

        // the first proposition is the most significant bit, the inverse of `as_bools`
        let n = bools.len();
        for (i, &b) in bools.iter().enumerate() {
            if b {
                raw.set(n - 1 - i)
            }
        }
        trace!("got {:?} from bools {:?}", raw, bools);

        Self {
            num_aps: bools.len() as u8,
            raw,
        }
    }
}

impl<RawTy: RawSymbolRepr> Display for PropSymbol<RawTy> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (0..self.num_aps)
            .rev()
            .try_for_each(|x| f.write_char(if self.raw.bit(x as usize) { '1' } else { '0' }))
    }
}

/// An expression over the atomic propositions of a [`PropAlphabet`]: a boolean formula,
/// represented as a truth table for few atomic propositions and as a BDD otherwise. It is satisfied by a set of [`PropSymbol`]s.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct PropExpression<RawTy: RawSymbolRepr = u32> {
    num_aps: u8,
    repr: Repr,
    _ty: PhantomData<RawTy>,
}

/// The number of atomic propositions up to which expressions are stored as truth tables.
const TABLE_APS: u8 = 6;

/// How an expression is stored. It is always a [`Repr::Table`] for at most [`TABLE_APS`]
/// propositions and a [`Repr::Bdd`] otherwise, so that equal expressions have equal
/// representations.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Repr {
    /// A truth table: bit `r` is set if the symbol with raw value `r` satisfies the expression.
    Table(u64),
    Bdd(Bdd),
}

/// The truth table that is satisfied by every symbol over `num_aps <= TABLE_APS` propositions.
fn full_table(num_aps: u8) -> u64 {
    if num_aps >= TABLE_APS {
        u64::MAX
    } else {
        (1u64 << (1u32 << num_aps)) - 1
    }
}

/// The position of the proposition `ap` in the raw value of a symbol: the first proposition is
/// the most significant bit.
fn raw_bit(num_aps: u8, ap: u8) -> usize {
    (num_aps - 1 - ap) as usize
}

/// Reverses the bits `0..num_aps` of `bits`, which turns bits indexed by proposition into bits of
/// a raw value and vice versa.
fn flip(num_aps: u8, bits: u128) -> u128 {
    if num_aps == 0 {
        0
    } else {
        bits.reverse_bits() >> (128 - num_aps as u32)
    }
}

/// The BDD of a truth table over `num_aps` propositions.
fn table_to_bdd(num_aps: u8, table: u64) -> Bdd {
    (0..1u64 << num_aps)
        .filter(|raw| table >> raw & 1 == 1)
        .fold(Bdd::bottom(), |acc, raw| {
            acc.or(&(0..num_aps).fold(Bdd::top(), |cube, ap| {
                let var = Bdd::var(ap);
                cube.and(&if raw >> raw_bit(num_aps, ap) & 1 == 1 {
                    var
                } else {
                    var.not()
                })
            }))
        })
}

impl Repr {
    fn and(&self, other: &Self) -> Self {
        match (self, other) {
            (Repr::Table(a), Repr::Table(b)) => Repr::Table(a & b),
            (Repr::Bdd(a), Repr::Bdd(b)) => Repr::Bdd(a.and(b)),
            _ => unreachable!("expressions over the same propositions are stored alike"),
        }
    }

    fn or(&self, other: &Self) -> Self {
        match (self, other) {
            (Repr::Table(a), Repr::Table(b)) => Repr::Table(a | b),
            (Repr::Bdd(a), Repr::Bdd(b)) => Repr::Bdd(a.or(b)),
            _ => unreachable!("expressions over the same propositions are stored alike"),
        }
    }

    fn is_unsatisfiable(&self) -> bool {
        match self {
            Repr::Table(table) => *table == 0,
            Repr::Bdd(bdd) => bdd.is_false(),
        }
    }
}

impl<RawTy: RawSymbolRepr> PropExpression<RawTy> {
    fn with_repr(num_aps: u8, repr: Repr) -> Self {
        Self {
            num_aps,
            repr,
            _ty: PhantomData,
        }
    }
    /// Parses an expression over `num_aps` atomic propositions in the syntax of labels in the HOA
    /// format: `t`, `f`, the index of a proposition, `!`, `&`, `|` (with decreasing precedence) and
    /// parentheses, for example `0 & !1` or `(0 & 1) | !2`.
    ///
    /// # Panics
    ///
    /// Panics if `string` is not a valid expression, see [`Self::try_new`].
    pub fn new(num_aps: u8, string: &str) -> PropExpression<RawTy> {
        Self::try_new(num_aps, string).expect("invalid expression")
    }
    /// Parses an expression like [`Self::new`].
    ///
    /// # Errors
    /// Returns [`PropAlphabetError::InvalidExpression`] if `string` is not an expression,
    /// [`PropAlphabetError::UnknownProposition`] if it mentions a proposition that is not smaller
    /// than `num_aps` and [`PropAlphabetError::TooManyAtomicPropositions`] if `num_aps` is larger
    /// than 128.
    pub fn try_new(num_aps: u8, string: &str) -> Result<Self, PropAlphabetError> {
        if num_aps as usize > MAX_APS {
            return Err(PropAlphabetError::TooManyAtomicPropositions {
                count: num_aps as usize,
                max: MAX_APS,
            });
        }
        let mut parser = Parser {
            input: string,
            position: 0,
            num_aps,
        };
        let expression = parser.or()?;
        parser.skip_whitespace();
        if parser.position < string.len() {
            return Err(parser.invalid());
        }
        Ok(expression)
    }
    /// Returns the expression that is satisfied by every symbol over `num_aps` atomic propositions.
    pub fn universal(num_aps: u8) -> Self {
        let repr = if num_aps > TABLE_APS {
            Repr::Bdd(Bdd::top())
        } else {
            Repr::Table(full_table(num_aps))
        };
        Self::with_repr(num_aps, repr)
    }
    /// Returns the expression that is satisfied by no symbol over `num_aps` atomic propositions.
    pub fn unsatisfiable(num_aps: u8) -> Self {
        let repr = if num_aps > TABLE_APS {
            Repr::Bdd(Bdd::bottom())
        } else {
            Repr::Table(0)
        };
        Self::with_repr(num_aps, repr)
    }
    /// Returns the expression that is satisfied by the symbols for which the atomic proposition
    /// with index `ap` holds.
    ///
    /// # Panics
    ///
    /// Panics if `ap >= num_aps` or `num_aps` is larger than 128.
    pub fn proposition(num_aps: u8, ap: u8) -> Self {
        assert!(ap < num_aps && num_aps as usize <= MAX_APS);
        let repr = if num_aps > TABLE_APS {
            Repr::Bdd(Bdd::var(ap))
        } else {
            Repr::Table(
                (0..1u64 << num_aps)
                    .filter(|raw| raw >> raw_bit(num_aps, ap) & 1 == 1)
                    .fold(0, |table, raw| table | 1 << raw),
            )
        };
        Self::with_repr(num_aps, repr)
    }
    /// Iterates over the symbols that satisfy the expression, for at most 6 atomic propositions in
    /// ascending order of their raw values.
    pub fn sat_vals(&self) -> PropExpressionSymbols<'_, RawTy> {
        PropExpressionSymbols {
            iter: match &self.repr {
                Repr::Table(table) => SymbolsIter::Table {
                    table: *table,
                    num_aps: self.num_aps,
                },
                Repr::Bdd(bdd) => SymbolsIter::Bdd {
                    cubes: Box::new(bdd.cubes()),
                    num_aps: self.num_aps,
                    current: None,
                },
            },
            _ty: PhantomData,
        }
    }
    /// Iterates over the letters that represent the symbols satisfying the expression.
    pub fn chars_iter(&self) -> impl Iterator<Item = char> + '_ {
        self.sat_vals().map(|e: PropSymbol<RawTy>| e.as_char())
    }
    /// The expression as cubes (paths to `true` of a BDD): propositions that are fixed and their
    /// values, indexed by proposition.
    fn cubes(&self) -> Vec<Cube> {
        match &self.repr {
            Repr::Table(table) => table_to_bdd(self.num_aps, *table).cubes().collect(),
            Repr::Bdd(bdd) => bdd.cubes().collect(),
        }
    }
}

/// The largest number of atomic propositions of an expression, the number of variables of the BDD
/// manager.
const MAX_APS: usize = 128;

/// A recursive descent parser for labels in HOA syntax.
struct Parser<'a> {
    input: &'a str,
    position: usize,
    num_aps: u8,
}

impl Parser<'_> {
    fn skip_whitespace(&mut self) {
        self.position += self.input[self.position..]
            .len()
            .saturating_sub(self.input[self.position..].trim_start().len());
    }
    fn invalid(&self) -> PropAlphabetError {
        PropAlphabetError::InvalidExpression {
            position: self.position,
        }
    }
    /// Consumes `c` if it is next.
    fn eat(&mut self, c: char) -> bool {
        self.skip_whitespace();
        let found = self.input[self.position..].starts_with(c);
        if found {
            self.position += c.len_utf8();
        }
        found
    }
    fn or<RawTy: RawSymbolRepr>(&mut self) -> Result<PropExpression<RawTy>, PropAlphabetError> {
        let mut left = self.and()?;
        while self.eat('|') {
            left |= self.and()?;
        }
        Ok(left)
    }
    fn and<RawTy: RawSymbolRepr>(&mut self) -> Result<PropExpression<RawTy>, PropAlphabetError> {
        let mut left = self.not()?;
        while self.eat('&') {
            left &= self.not()?;
        }
        Ok(left)
    }
    fn not<RawTy: RawSymbolRepr>(&mut self) -> Result<PropExpression<RawTy>, PropAlphabetError> {
        if self.eat('!') {
            return Ok(!self.not()?);
        }
        self.atom()
    }
    fn atom<RawTy: RawSymbolRepr>(&mut self) -> Result<PropExpression<RawTy>, PropAlphabetError> {
        if self.eat('(') {
            let inner = self.or()?;
            return if self.eat(')') {
                Ok(inner)
            } else {
                Err(self.invalid())
            };
        }
        if self.eat('t') {
            return Ok(PropExpression::universal(self.num_aps));
        }
        if self.eat('f') {
            return Ok(PropExpression::unsatisfiable(self.num_aps));
        }
        let rest = &self.input[self.position..];
        let digits = rest.len() - rest.trim_start_matches(|c: char| c.is_ascii_digit()).len();
        if digits == 0 {
            return Err(self.invalid());
        }
        let ap: usize = rest[..digits].parse().map_err(|_| self.invalid())?;
        if ap >= self.num_aps as usize {
            return Err(PropAlphabetError::UnknownProposition {
                ap,
                num_aps: self.num_aps,
            });
        }
        self.position += digits;
        Ok(PropExpression::proposition(self.num_aps, ap as u8))
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitAnd for PropExpression<RawTy> {
    type Output = PropExpression<RawTy>;

    fn bitand(self, rhs: Self) -> Self::Output {
        assert_eq!(self.num_aps, rhs.num_aps);
        PropExpression {
            num_aps: self.num_aps,
            repr: self.repr.and(&rhs.repr),
            _ty: PhantomData,
        }
    }
}
impl<RawTy: RawSymbolRepr> std::ops::Not for PropExpression<RawTy> {
    type Output = PropExpression<RawTy>;

    fn not(self) -> Self::Output {
        let repr = match &self.repr {
            Repr::Table(table) => Repr::Table(!table & full_table(self.num_aps)),
            Repr::Bdd(bdd) => Repr::Bdd(bdd.not()),
        };
        Self {
            num_aps: self.num_aps,
            repr,
            _ty: PhantomData,
        }
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitOr for PropExpression<RawTy> {
    type Output = PropExpression<RawTy>;
    fn bitor(self, rhs: Self) -> Self::Output {
        assert_eq!(self.num_aps, rhs.num_aps);
        Self {
            num_aps: self.num_aps,
            repr: self.repr.or(&rhs.repr),
            _ty: PhantomData,
        }
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitAndAssign for PropExpression<RawTy> {
    fn bitand_assign(&mut self, rhs: Self) {
        assert_eq!(self.num_aps, rhs.num_aps);
        self.repr = self.repr.and(&rhs.repr);
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitOrAssign for PropExpression<RawTy> {
    fn bitor_assign(&mut self, rhs: Self) {
        assert_eq!(self.num_aps, rhs.num_aps);
        self.repr = self.repr.or(&rhs.repr);
    }
}

impl<RawTy: RawSymbolRepr> PartialOrd for PropExpression<RawTy> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<RawTy: RawSymbolRepr> Ord for PropExpression<RawTy> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sat_vals()
            .map(|symbol| symbol.as_bools())
            .min()
            .cmp(&other.sat_vals().map(|symbol| symbol.as_bools()).min())
    }
}

impl<RawTy: RawSymbolRepr> PropExpression<RawTy> {
    /// Renders the expression as a disjunction of conjunctions of literals, whose propositions are
    /// named by `name`. The result follows the structure of the BDD, not the history of the BDD
    /// manager. The constants are rendered as `t` and `f`.
    fn render(&self, name: impl Fn(u8) -> String, and: &str) -> String {
        let cubes = self.cubes();
        let clauses = cubes
            .iter()
            .map(|cube| {
                (0..self.num_aps)
                    .filter(|&ap| cube.care >> ap & 1 == 1)
                    .map(|ap| {
                        if cube.value >> ap & 1 == 1 {
                            name(ap)
                        } else {
                            format!("!{}", name(ap))
                        }
                    })
                    .join(and)
            })
            .collect_vec();
        match &clauses[..] {
            [] => "f".to_string(),
            [clause] if clause.is_empty() => "t".to_string(),
            [clause] => clause.clone(),
            _ => clauses.into_iter().map(|c| format!("({c})")).join(" | "),
        }
    }
    /// Renders the expression as a label in the HOA format, i.e. over the indices of the atomic
    /// propositions, for example `0 & !1` or `(0 & 1) | (!0 & !1)`. The label is not minimal.
    /// [`Self::try_new`] parses it back.
    pub fn to_hoa_label(&self) -> String {
        self.render(|i| i.to_string(), " & ")
    }
}

/// Renders the expression over the letters `a`, `b`, ... instead of the proposition indices.
impl<RawTy: RawSymbolRepr> Display for PropExpression<RawTy> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.render(|i| ((b'a' + i) as char).to_string(), "&"))
    }
}

impl<RawTy: RawSymbolRepr> Matcher<PropExpression<RawTy>> for PropSymbol<RawTy> {
    fn matches(&self, expression: &PropExpression<RawTy>) -> bool {
        assert_eq!(self.num_aps, expression.num_aps);
        match &expression.repr {
            Repr::Table(table) => table >> self.raw.as_usize() & 1 == 1,
            Repr::Bdd(bdd) => bdd.eval(self.num_aps, |ap| self.raw.bit(raw_bit(self.num_aps, ap))),
        }
    }
}

impl<RawTy: RawSymbolRepr> Matcher<PropExpression<RawTy>> for PropExpression<RawTy> {
    fn matches(&self, expression: &PropExpression<RawTy>) -> bool {
        assert_eq!(self.num_aps, expression.num_aps);
        // all values in self should also be in expression
        // we share nothing with the complement of the expression
        match (&self.repr, &expression.repr) {
            (Repr::Table(a), Repr::Table(b)) => a & !b == 0,
            (Repr::Bdd(a), Repr::Bdd(b)) => a.and(&b.not()).is_false(),
            _ => unreachable!("expressions over the same propositions are stored alike"),
        }
    }
}

impl<RawTy: RawSymbolRepr> Expression for PropExpression<RawTy> {
    type S = PropSymbol<RawTy>;

    type SymbolsIter<'this>
        = PropExpressionSymbols<'this, RawTy>
    where
        Self: 'this;

    fn symbols(&self) -> Self::SymbolsIter<'_> {
        self.sat_vals()
    }

    fn intersection(&self, other: &Self) -> Option<Self> {
        if self.num_aps != other.num_aps {
            return None;
        }
        let repr = self.repr.and(&other.repr);
        (!repr.is_unsatisfiable()).then_some(PropExpression {
            num_aps: self.num_aps,
            repr,
            _ty: PhantomData,
        })
    }

    /// Two expressions overlap if some symbol satisfies both. Expressions over a different
    /// number of atomic propositions never overlap.
    fn overlaps(&self, other: &Self) -> bool {
        self.num_aps == other.num_aps && !self.repr.and(&other.repr).is_unsatisfiable()
    }
}

/// An iterator over the [`PropSymbol`]s that satisfy a [`PropExpression`].
pub struct PropExpressionSymbols<'a, RawTy: RawSymbolRepr> {
    iter: SymbolsIter<'a>,
    _ty: PhantomData<RawTy>,
}

enum SymbolsIter<'a> {
    /// The remaining set bits of a truth table.
    Table { table: u64, num_aps: u8 },
    /// The cubes of a BDD, of which the one that is currently expanded is `current`.
    Bdd {
        cubes: Box<dyn Iterator<Item = Cube> + 'a>,
        num_aps: u8,
        current: Option<Expansion>,
    },
}

/// The symbols of a cube in raw form: `fixed` plus every subset `sub` of `free`. The next one to
/// yield is `sub`.
struct Expansion {
    fixed: u128,
    free: u128,
    sub: u128,
    done: bool,
}

impl<RawTy: RawSymbolRepr> Iterator for PropExpressionSymbols<'_, RawTy> {
    type Item = PropSymbol<RawTy>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            SymbolsIter::Table { table, num_aps } => {
                if *table == 0 {
                    return None;
                }
                let raw = table.trailing_zeros() as usize;
                *table &= *table - 1;
                Some(PropSymbol {
                    num_aps: *num_aps,
                    raw: RawTy::from_usize(raw),
                })
            }
            SymbolsIter::Bdd {
                cubes,
                num_aps,
                current,
            } => loop {
                let Some(expansion) = current else {
                    let cube = cubes.next()?;
                    let all = flip(*num_aps, !0);
                    let care = flip(*num_aps, cube.care);
                    let free = all & !care;
                    *current = Some(Expansion {
                        fixed: flip(*num_aps, cube.value),
                        free,
                        sub: free,
                        done: false,
                    });
                    continue;
                };
                if expansion.done {
                    *current = None;
                    continue;
                }
                let raw = expansion.fixed | expansion.sub;
                if expansion.sub == 0 {
                    expansion.done = true;
                } else {
                    expansion.sub = (expansion.sub - 1) & expansion.free;
                }
                let mut symbol = RawTy::from_usize(0);
                (0..*num_aps as usize)
                    .filter(|bit| raw >> bit & 1 == 1)
                    .for_each(|bit| symbol.set(bit));
                return Some(PropSymbol {
                    num_aps: *num_aps,
                    raw: symbol,
                });
            },
        }
    }
}

/// Represents a propositional alphabet, which consists of a list of atomic propositions.
///
/// A symbol of this alphabet simply a valuation of the atomic propositions, which is
/// represented as a binary string of length `num_aps` (whose limit gets determined by
/// the number of bits in the type parameter `RawTy`).
///
/// An Expression is represented by a boolean formula over the atomic propositions. Here,
/// we store it as a [`PropExpression`], a truth table or a BDD.
///
/// # Example
/// Assume we have a propositional alphabet over the atomic propositions `a`, `b` and `c`.
///
/// Then a **symbol** in this alphabet is a valuation of these variables, e.g. `a & !b & c`.
///
/// An **expression** on the other hand is used to label edges and it is a boolean expression over
/// the atomic propositions, e.g. `(a | b) & c`. Such an expression is matched by
/// a symbol if the symbol satisfies the expression, i.e. if the expression evaluates to `true` under the given
/// valuation. The expression from above, for example, would be matched by the symbol given above (`a & !b & c`),
/// but not by the symbols `a & b & !c` or `!a & !b & c`.
#[derive(Clone, Debug)]
pub struct PropAlphabet<RawTy: RawSymbolRepr = u32> {
    aps: Vec<String>,
    universal: PropExpression<RawTy>,
}

/// Two alphabets are equal if they have the same atomic propositions in the same order: symbols
/// are bit vectors indexed by position, so a permutation is a different alphabet.
impl<RawTy: RawSymbolRepr> PartialEq for PropAlphabet<RawTy> {
    fn eq(&self, other: &Self) -> bool {
        self.aps == other.aps
    }
}

impl<RawTy: RawSymbolRepr> Eq for PropAlphabet<RawTy> {}

impl<RawTy: RawSymbolRepr> PropAlphabet<RawTy> {
    /// Creates a new alphabet over the atomic propositions with the given names.
    ///
    /// # Panics
    /// Panics if `aps` is empty or contains too many names, see [`Self::try_new`] for a
    /// fallible version.
    pub fn new(aps: Vec<String>) -> Self {
        Self::try_new(aps).expect("invalid atomic propositions")
    }

    /// Creates a new alphabet over the atomic propositions with the given names.
    ///
    /// # Errors
    /// Returns an error if `aps` is empty ([`PropAlphabetError::NoAtomicPropositions`]) or
    /// contains too many names ([`PropAlphabetError::TooManyAtomicPropositions`]).
    pub fn try_new(aps: Vec<String>) -> Result<Self, PropAlphabetError> {
        if aps.is_empty() {
            return Err(PropAlphabetError::NoAtomicPropositions);
        }
        if aps.len() >= RawTy::max_aps() {
            return Err(PropAlphabetError::TooManyAtomicPropositions {
                count: aps.len(),
                max: RawTy::max_aps() - 1,
            });
        }

        let universal = PropExpression::<RawTy>::universal(aps.len() as u8);
        Ok(Self { universal, aps })
    }

    /// Returns the number of atomic propositions.
    pub fn aps(&self) -> u8 {
        self.aps.len() as u8
    }

    /// Converts a letter into the corresponding symbol of this alphabet.
    ///
    /// # Panics
    ///
    /// Panics if `value` is smaller than `'a'`.
    pub fn char_to_symbol(&self, value: char) -> PropSymbol<RawTy> {
        assert!(value >= 'a');

        let raw = RawTy::from_usize(((value as u8) - b'a') as usize);
        PropSymbol {
            raw,
            num_aps: self.aps(),
        }
    }

    /// Converts a symbol of this alphabet into a letter.
    ///
    /// # Panics
    ///
    /// Panics if the symbol was created for a different number of atomic propositions than this
    /// alphabet has, or if there are too many atomic propositions.
    pub fn hoa_symbol_to_char(&self, sym: &PropSymbol<RawTy>) -> char {
        assert_eq!(sym.num_aps, self.aps(), "symbol does not match alphabet");
        assert!((sym.num_aps as usize) < RawTy::max_aps(), "too many aps");

        (b'a' + (sym.raw.as_usize() as u8)) as char
    }

    /// Returns the number of symbols of the alphabet, `2^n` for `n` atomic propositions.
    pub fn size(&self) -> usize {
        2usize.saturating_pow(self.aps() as u32)
    }
    /// Returns the names of the atomic propositions.
    pub fn apnames(&self) -> &[String] {
        &self.aps
    }

    /// Attempts to build an instance of `Self` from the given pointer to a [`CharAlphabet`]. This
    /// only works (for the moment) if the number of symbols in the given alphabet is an exact
    /// power of two.
    ///
    /// # Errors
    /// Returns [`PropAlphabetError::InvalidSize`] if the size is not a power of two or is
    /// smaller than two (that would require zero atomic propositions).
    pub fn try_from_char_alphabet(value: &CharAlphabet) -> Result<Self, PropAlphabetError> {
        let alphabet_size = value.size();
        if alphabet_size < 2 || !alphabet_size.is_power_of_two() {
            return Err(PropAlphabetError::InvalidSize(alphabet_size));
        }

        let aps = alphabet_size.ilog2() as u8;

        Self::try_from_apnames((0u8..aps).map(|i| ((b'a' + i) as char).to_string()))
    }

    /// Creates a new alphabet from the names of the atomic propositions.
    ///
    /// # Panics
    /// Panics if there are no names or too many, see [`Self::try_from_apnames`].
    pub fn from_apnames<I>(apnames: I) -> Self
    where
        I: IntoIterator,
        I::Item: Display,
    {
        Self::try_from_apnames(apnames).expect("invalid atomic propositions")
    }

    /// Creates a new alphabet from the names of the atomic propositions.
    ///
    /// # Errors
    /// See [`Self::try_new`].
    pub fn try_from_apnames<I>(apnames: I) -> Result<Self, PropAlphabetError>
    where
        I: IntoIterator,
        I::Item: Display,
    {
        let apnames: Vec<_> = apnames.into_iter().map(|i| i.to_string()).collect();
        Self::try_new(apnames)
    }
}

impl<RawTy: RawSymbolRepr> Alphabet for PropAlphabet<RawTy> {
    type Symbol = PropSymbol<RawTy>;

    type Expression = PropExpression<RawTy>;

    fn try_make_expression(&self, symbol: Self::Symbol) -> Option<Self::Expression> {
        if symbol.num_aps as usize != self.aps.len() {
            return None;
        }
        Some(symbol.as_expression())
    }

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        left.overlaps(right)
    }

    type Universe<'this>
        = PropExpressionSymbols<'this, RawTy>
    where
        Self: 'this;

    fn universe(&self) -> Self::Universe<'_> {
        self.universal.sat_vals()
    }

    fn contains(&self, symbol: Self::Symbol) -> bool {
        symbol.num_aps == self.aps() && symbol.raw.as_usize() < self.size()
    }

    fn size(&self) -> usize {
        2usize.saturating_pow(self.aps.len() as u32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn expressions_are_rendered_over_indices_for_hoa_and_letters_for_humans() {
        let both = PropExpression::<u32>::new(2, "0 & !1");
        assert_eq!(both.to_hoa_label(), "0 & !1");
        assert_eq!(both.to_string(), "a&!b");

        let either = PropExpression::<u32>::new(2, "0 | 1");
        let label = either.to_hoa_label();
        assert!(label.contains(" | "), "{label}");
        assert!(
            !label.contains(|c: char| c.is_ascii_alphabetic()),
            "{label}"
        );

        let always = PropExpression::<u32>::universal(2);
        assert_eq!(always.to_hoa_label(), "t");
        let never = PropExpression::<u32>::new(2, "0 & !0");
        assert_eq!(never.to_hoa_label(), "f");
        assert_eq!(never.to_string(), "f");
    }

    #[test]
    fn intersection_of_expressions_is_their_conjunction_if_satisfiable() {
        let expression = |s| PropExpression::<u32>::new(2, s);
        let (first, second) = (expression("0"), expression("1"));
        assert_eq!(first.intersection(&second), Some(expression("0 & 1")));
        assert_eq!(
            PropExpression::universal(2).intersection(&first),
            Some(first.clone())
        );
        assert_eq!(first.intersection(&expression("!0")), None);
        assert_eq!(first.intersection(&PropExpression::universal(1)), None);
        assert_eq!('a'.intersection(&'a'), Some('a'));
        assert_eq!('a'.intersection(&'b'), None);
    }

    #[test]
    fn try_new_validates_the_number_of_atomic_propositions() {
        assert!(matches!(
            PropAlphabet::<u32>::try_new(vec![]),
            Err(PropAlphabetError::NoAtomicPropositions)
        ));
        let too_many = (0..40).map(|i| i.to_string()).collect();
        assert!(matches!(
            PropAlphabet::<u32>::try_new(too_many),
            Err(PropAlphabetError::TooManyAtomicPropositions { count: 40, .. })
        ));
        assert!(PropAlphabet::<u32>::try_new(vec!["a".into(), "b".into()]).is_ok());
    }

    #[test]
    fn char_alphabet_conversion_requires_power_of_two_size() {
        for size in [0, 1, 3, 5, 6, 7] {
            assert!(matches!(
                PropAlphabet::<u32>::try_from_char_alphabet(&CharAlphabet::of_size(size)),
                Err(PropAlphabetError::InvalidSize(s)) if s == size
            ));
        }
        for (size, aps) in [(2, 1), (4, 2), (8, 3)] {
            let converted =
                PropAlphabet::<u32>::try_from_char_alphabet(&CharAlphabet::of_size(size)).unwrap();
            assert_eq!(converted.aps(), aps);
        }
    }

    #[test]
    fn alphabet_contains_only_its_own_symbols() {
        let alphabet: PropAlphabet = PropAlphabet::new(vec!["a".into(), "b".into()]);
        assert!(alphabet.contains(alphabet.char_to_symbol('a')));
        assert!(alphabet.contains(alphabet.char_to_symbol('d')));
        // raw value 7 needs three atomic propositions
        assert!(!alphabet.contains(alphabet.char_to_symbol('h')));
        // symbol over a different number of atomic propositions
        let other: PropAlphabet = PropAlphabet::new(vec!["a".into(), "b".into(), "c".into()]);
        assert!(!alphabet.contains(other.char_to_symbol('a')));
    }

    /// A random expression, to be compared against a brute-force evaluation.
    #[derive(Debug, Clone)]
    enum Tree {
        True,
        False,
        Ap(u8),
        Not(Box<Tree>),
        And(Box<Tree>, Box<Tree>),
        Or(Box<Tree>, Box<Tree>),
    }

    impl Tree {
        /// Whether the symbol with raw value `raw` over `n` propositions satisfies the tree.
        fn eval(&self, n: u8, raw: u32) -> bool {
            match self {
                Tree::True => true,
                Tree::False => false,
                Tree::Ap(ap) => raw >> (n - 1 - ap) & 1 == 1,
                Tree::Not(t) => !t.eval(n, raw),
                Tree::And(l, r) => l.eval(n, raw) && r.eval(n, raw),
                Tree::Or(l, r) => l.eval(n, raw) || r.eval(n, raw),
            }
        }
        fn build(&self, n: u8) -> PropExpression<u32> {
            match self {
                Tree::True => PropExpression::universal(n),
                Tree::False => PropExpression::unsatisfiable(n),
                Tree::Ap(ap) => PropExpression::proposition(n, *ap),
                Tree::Not(t) => !t.build(n),
                Tree::And(l, r) => l.build(n) & r.build(n),
                Tree::Or(l, r) => l.build(n) | r.build(n),
            }
        }
        fn text(&self) -> String {
            match self {
                Tree::True => "t".into(),
                Tree::False => "f".into(),
                Tree::Ap(ap) => ap.to_string(),
                Tree::Not(t) => format!("!{}", t.text()),
                Tree::And(l, r) => format!("({} & {})", l.text(), r.text()),
                Tree::Or(l, r) => format!("({} | {})", l.text(), r.text()),
            }
        }
    }

    fn trees() -> impl Strategy<Value = (u8, Tree, Tree)> {
        (1u8..=10).prop_flat_map(|n| {
            let tree = prop_oneof![
                Just(Tree::True),
                Just(Tree::False),
                (0..n).prop_map(Tree::Ap)
            ]
            .prop_recursive(5, 40, 2, |inner| {
                prop_oneof![
                    inner.clone().prop_map(|t| Tree::Not(Box::new(t))),
                    (inner.clone(), inner.clone())
                        .prop_map(|(l, r)| Tree::And(Box::new(l), Box::new(r))),
                    (inner.clone(), inner).prop_map(|(l, r)| Tree::Or(Box::new(l), Box::new(r))),
                ]
            });
            (Just(n), tree.clone(), tree)
        })
    }

    proptest! {
        /// Expressions behave like the truth table that is computed by brute force, for the table
        /// representation (up to 6 propositions) and for BDDs (7 to 10).
        #[test]
        fn expressions_agree_with_brute_force((n, left, right) in trees()) {
            let all: Vec<u32> = (0..1u32 << n).collect();
            let sat = |t: &Tree| all.iter().copied().filter(|&r| t.eval(n, r)).collect::<Vec<_>>();
            let (a, b) = (left.build(n), right.build(n));
            let symbols = |e: &PropExpression<u32>| {
                let mut raws = e.sat_vals().map(|s| s.raw).collect::<Vec<_>>();
                raws.sort();
                raws
            };
            prop_assert_eq!(symbols(&a), sat(&left));
            prop_assert_eq!(a.repr.is_unsatisfiable(), sat(&left).is_empty());
            // parsing, rendering and the operators
            prop_assert_eq!(&PropExpression::<u32>::try_new(n, &left.text()).unwrap(), &a);
            prop_assert_eq!(&PropExpression::<u32>::try_new(n, &a.to_hoa_label()).unwrap(), &a);
            let and = Tree::And(Box::new(left.clone()), Box::new(right.clone()));
            let or = Tree::Or(Box::new(left.clone()), Box::new(right.clone()));
            prop_assert_eq!(symbols(&(a.clone() & b.clone())), sat(&and));
            prop_assert_eq!(symbols(&(a.clone() | b.clone())), sat(&or));
            prop_assert_eq!(symbols(&!a.clone()), sat(&Tree::Not(Box::new(left.clone()))));
            let common = sat(&and);
            prop_assert_eq!(a.overlaps(&b), !common.is_empty());
            prop_assert_eq!(a.intersection(&b).map(|e| symbols(&e)), (!common.is_empty()).then_some(common));
            prop_assert_eq!(a.matches(&b), sat(&left).iter().all(|&r| right.eval(n, r)));
            for &raw in &all {
                let symbol = PropSymbol { num_aps: n, raw };
                prop_assert_eq!(symbol.matches(&a), left.eval(n, raw));
            }
            prop_assert_eq!(a == b, sat(&left) == sat(&right));
        }
    }

    #[test]
    fn parsing_rejects_invalid_expressions() {
        let parse = |n, s| PropExpression::<u32>::try_new(n, s);
        assert_eq!(
            parse(2, "0 &"),
            Err(PropAlphabetError::InvalidExpression { position: 3 })
        );
        assert!(matches!(
            parse(2, "(0 | 1"),
            Err(PropAlphabetError::InvalidExpression { .. })
        ));
        assert!(matches!(
            parse(2, "0 1"),
            Err(PropAlphabetError::InvalidExpression { .. })
        ));
        assert_eq!(
            parse(2, "0 & 2"),
            Err(PropAlphabetError::UnknownProposition { ap: 2, num_aps: 2 })
        );
        assert!(matches!(
            parse(200, "t"),
            Err(PropAlphabetError::TooManyAtomicPropositions { .. })
        ));
        // precedence: ! binds tighter than &, which binds tighter than |
        assert_eq!(
            parse(3, "0 | 1 & !2").unwrap(),
            parse(3, "0 | (1 & (!2))").unwrap()
        );
        assert_eq!(parse(2, " ( 0 ) ").unwrap(), parse(2, "0").unwrap());
    }

    #[test]
    fn rendering_does_not_depend_on_the_history_of_the_manager() {
        let text = "(0 & !8) | (3 & 9) | (!5 & 7)";
        let before = PropExpression::<u32>::new(10, text).to_hoa_label();
        // unrelated BDD work changes the node ids that the next expression gets
        let noise = PropExpression::<u32>::new(10, "(1 & 2 & !4) | (6 & !9)");
        let _ = (noise.clone() | !noise).to_hoa_label();
        assert_eq!(PropExpression::<u32>::new(10, text).to_hoa_label(), before);
    }

    #[test]
    fn expressions_can_be_built_in_threads_and_combined() {
        let parts: Vec<_> = (0..8u8)
            .map(|ap| {
                std::thread::spawn(move || {
                    PropExpression::<u32>::proposition(9, ap)
                        | PropExpression::proposition(9, ap + 1)
                })
            })
            .collect();
        let combined = parts
            .into_iter()
            .map(|t| t.join().unwrap())
            .fold(PropExpression::universal(9), |acc, e| acc & e);
        assert_eq!(
            combined,
            PropExpression::<u32>::new(
                9,
                "(0|1) & (1|2) & (2|3) & (3|4) & (4|5) & (5|6) & (6|7) & (7|8)"
            )
        );
    }

    #[test]
    fn expressions_over_many_propositions_use_bdds() {
        let (x, y) = (
            PropExpression::<u32>::new(8, "0 & 7"),
            PropExpression::new(8, "!0"),
        );
        assert!(!x.overlaps(&y));
        assert!(x.overlaps(&PropExpression::universal(8)));
        assert_eq!(x.sat_vals().count(), 64);
        assert_eq!((x.clone() | y.clone()).sat_vals().count(), 128 + 64);
    }

    #[test]
    fn expression_overlaps() {
        let a_and_b = PropExpression::<u32>::new(2, "0 & 1");
        let a = PropExpression::<u32>::new(2, "0");
        let not_a = PropExpression::<u32>::new(2, "!0");
        assert!(a_and_b.overlaps(&a));
        assert!(a.overlaps(&a_and_b));
        assert!(!a.overlaps(&not_a));
        // different numbers of atomic propositions never overlap
        assert!(!a.overlaps(&PropExpression::<u32>::new(3, "0")));
    }

    #[test]
    fn prop_symbol() {
        let ps = PropSymbol {
            num_aps: 5,
            raw: 19u32,
        };
        assert_eq!(ps.to_string(), "10011".to_string());
    }

    #[test]
    fn bools_round_trip() {
        for n in 0..=5u32 {
            for raw in 0..(1u32 << n) {
                let symbol = PropSymbol {
                    num_aps: n as u8,
                    raw,
                };
                assert_eq!(PropSymbol::from_bools(symbol.as_bools()), symbol);
            }
        }
    }

    #[test]
    fn prop_expression() {
        let pe = PropExpression::<u32>::new(3, "0 | (1 & 2)");

        assert!(PropSymbol::from_bools(vec![false, true, true]).matches(&pe));
        assert!(PropSymbol::from_bools(vec![false, true, true]).matches(&pe));
        assert!(!PropSymbol::from_bools(vec![false, false, false]).matches(&pe));
    }
}
