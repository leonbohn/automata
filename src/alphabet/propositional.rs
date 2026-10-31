use std::{
    fmt::Display,
    hash::Hash,
    marker::PhantomData,
    sync::{Arc, Mutex},
};

use biodivine_lib_bdd::{Bdd, BddSatisfyingValuations, BddValuation, BddVariableSet};
use itertools::Itertools;
use thiserror::Error;
use tracing::trace;

use crate::show::Show;
use std::collections::BTreeSet;

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
        PropExpression::from_parts(self.num_aps, self.as_bdd_valuation().into())
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
    /// Creates a symbol from a valuation of the atomic propositions.
    ///
    /// # Panics
    ///
    /// Panics if there are more booleans than the representation can hold.
    pub fn from_bools(bools: Vec<bool>) -> Self {
        assert!(bools.len() <= 8usize.saturating_pow(std::mem::size_of::<RawTy>() as u32));
        let mut raw = RawTy::from_usize(0);

        (0..bools.len()).rev().for_each(|i| {
            if bools[i] {
                raw.set(i)
            }
        });
        trace!("got {:?} from bools {:?}", raw, bools);

        Self {
            num_aps: bools.len() as u8,
            raw,
        }
    }
    /// Converts the symbol into a valuation of the variables of a BDD.
    pub fn as_bdd_valuation(&self) -> BddValuation {
        BddValuation::new(self.as_bools())
    }
    /// Creates a symbol from a valuation of the variables of a BDD.
    pub fn from_bdd_valuation(val: BddValuation) -> Self {
        Self::from_bools(val.into_vector())
    }
}

impl<RawTy: RawSymbolRepr> Show for PropSymbol<RawTy> {
    fn show(&self) -> String {
        let chr = |b| {
            if b { '1' } else { '0' }
        };
        assert!(
            self.num_aps as usize <= 8usize.saturating_pow(std::mem::size_of::<RawTy>() as u32)
        );
        (0..self.num_aps).rev().fold(
            String::with_capacity(self.num_aps as usize),
            |mut acc, x| {
                acc.push(chr(self.raw.bit(x as usize)));
                acc
            },
        )
    }
}

/// An expression over the atomic propositions of a [`PropAlphabet`]: a boolean formula,
/// represented as a BDD. It is satisfied by a set of [`PropSymbol`]s.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct PropExpression<RawTy: RawSymbolRepr = u32> {
    num_aps: u8,
    bdd: Bdd,
    _ty: PhantomData<RawTy>,
}

impl<RawTy: RawSymbolRepr> PropExpression<RawTy> {
    /// Creates an expression over `num_aps` atomic propositions from the given BDD.
    pub fn from_parts(num_aps: u8, bdd: Bdd) -> Self {
        Self {
            num_aps,
            bdd,
            _ty: PhantomData,
        }
    }
    /// Parses an expression over `num_aps` atomic propositions, whose variables are named `x_0`,
    /// `x_1`, ..., for example `x_0 & !x_1`.
    ///
    /// # Panics
    ///
    /// Panics if `string` is not a valid expression.
    pub fn new(num_aps: u8, string: &str) -> PropExpression<RawTy> {
        let vars = BddVariableSet::new_anonymous(num_aps as u16);
        Self::from_parts(num_aps, vars.eval_expression_string(string))
    }
    /// Returns the underlying BDD.
    pub fn into_bdd(self) -> Bdd {
        self.bdd
    }
    /// Returns the expression that is satisfied by every symbol over `num_aps` atomic propositions.
    pub fn universal(num_aps: u8) -> Self {
        let vars = BddVariableSet::new_anonymous(num_aps as u16);
        Self {
            num_aps,
            bdd: vars.mk_true(),
            _ty: PhantomData,
        }
    }
    /// Iterates over the symbols that satisfy the expression.
    pub fn sat_vals(&self) -> PropExpressionSymbols<'_, RawTy> {
        PropExpressionSymbols {
            iter: self.bdd.sat_valuations(),
            _ty: PhantomData,
        }
    }
    /// Creates an expression from a BDD over the atomic propositions.
    ///
    /// # Panics
    ///
    /// Panics if the BDD has more than 255 variables.
    pub fn from_bdd(bdd: Bdd) -> Self {
        Self {
            num_aps: bdd
                .num_vars()
                .try_into()
                .expect("Number of variables does not fit into u8"),
            bdd,
            _ty: PhantomData,
        }
    }
    /// Iterates over the letters that represent the symbols satisfying the expression.
    pub fn chars_iter(&self) -> impl Iterator<Item = char> + '_ {
        PropExpressionSymbols {
            iter: self.bdd.sat_valuations(),
            _ty: PhantomData,
        }
        .map(|e: PropSymbol<RawTy>| e.as_char())
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitAnd for PropExpression<RawTy> {
    type Output = PropExpression<RawTy>;

    fn bitand(self, rhs: Self) -> Self::Output {
        assert_eq!(self.num_aps, rhs.num_aps);
        PropExpression {
            num_aps: self.num_aps,
            bdd: self.bdd.and(&rhs.bdd),
            _ty: PhantomData,
        }
    }
}
impl<RawTy: RawSymbolRepr> std::ops::Not for PropExpression<RawTy> {
    type Output = PropExpression<RawTy>;

    fn not(self) -> Self::Output {
        Self::from_parts(self.num_aps, self.bdd.not())
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitOr for PropExpression<RawTy> {
    type Output = PropExpression<RawTy>;
    fn bitor(self, rhs: Self) -> Self::Output {
        assert_eq!(self.num_aps, rhs.num_aps);
        Self::from_parts(self.num_aps, self.bdd.or(&rhs.bdd))
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitAndAssign for PropExpression<RawTy> {
    fn bitand_assign(&mut self, rhs: Self) {
        assert_eq!(self.num_aps, rhs.num_aps);
        *self = Self::from_parts(self.num_aps, self.bdd.and(&rhs.bdd));
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitOrAssign for PropExpression<RawTy> {
    fn bitor_assign(&mut self, rhs: Self) {
        assert_eq!(self.num_aps, rhs.num_aps);
        *self = Self::from_parts(self.num_aps, self.bdd.or(&rhs.bdd));
    }
}

impl<RawTy: RawSymbolRepr> PartialOrd for PropExpression<RawTy> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<RawTy: RawSymbolRepr> Ord for PropExpression<RawTy> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.bdd
            .sat_valuations()
            .min()
            .cmp(&other.bdd.sat_valuations().min())
    }
}

/// Renders a BDD as a disjunction of conjunctions (its optimized DNF). The variable with index
/// `i` is rendered as `name(i)`, conjunctions are joined by `and`. The constants are rendered as
/// `t` and `f`.
fn bdd_to_string(bdd: &Bdd, name: impl Fn(usize) -> String, and: &str) -> String {
    if bdd.is_true() {
        return "t".to_string();
    }
    if bdd.is_false() {
        return "f".to_string();
    }
    let dnf = bdd.to_optimized_dnf();
    let clauses = dnf
        .iter()
        .map(|clause| {
            let mut vals = clause.to_values();
            vals.sort();
            vals.into_iter()
                .map(|(v, b)| {
                    let name = name(v.to_index());
                    if b { name } else { format!("!{name}") }
                })
                .join(and)
        })
        .collect_vec();
    if clauses.len() > 1 {
        clauses.into_iter().map(|c| format!("({c})")).join(" | ")
    } else {
        clauses.into_iter().next().unwrap_or_default()
    }
}

impl<RawTy: RawSymbolRepr> PropExpression<RawTy> {
    /// Renders the expression as a label in the HOA format, i.e. over the indices of the atomic
    /// propositions, for example `0 & !1` or `(0 & 1) | (!0 & !1)`.
    pub fn to_hoa_label(&self) -> String {
        bdd_to_string(&self.bdd, |i| i.to_string(), " & ")
    }
}

impl<RawTy: RawSymbolRepr> Show for PropExpression<RawTy> {
    /// Renders the expression over the letters `a`, `b`, ... instead of the proposition indices.
    fn show(&self) -> String {
        bdd_to_string(&self.bdd, |i| ((b'a' + i as u8) as char).to_string(), "&")
    }
}

impl<RawTy: RawSymbolRepr> Matcher<PropExpression<RawTy>> for PropSymbol<RawTy> {
    fn matches(&self, expression: &PropExpression<RawTy>) -> bool {
        assert_eq!(self.num_aps, expression.num_aps);
        expression.bdd.eval_in(&self.as_bdd_valuation())
    }
}

impl<RawTy: RawSymbolRepr> Matcher<PropExpression<RawTy>> for PropExpression<RawTy> {
    fn matches(&self, expression: &PropExpression<RawTy>) -> bool {
        assert_eq!(self.num_aps, expression.num_aps);
        // all values in self should also be in expression
        // we share nothing with the complement of the expression
        expression.bdd.not().and(&self.bdd).sat_witness().is_none()
    }
}

impl<RawTy: RawSymbolRepr> Expression for PropExpression<RawTy> {
    type S = PropSymbol<RawTy>;

    type SymbolsIter<'this>
        = PropExpressionSymbols<'this, RawTy>
    where
        Self: 'this;

    fn symbols(&self) -> Self::SymbolsIter<'_> {
        PropExpressionSymbols {
            iter: self.bdd.sat_valuations(),
            _ty: PhantomData::<RawTy>,
        }
    }

    /// Two expressions overlap if some symbol satisfies both. Expressions over a different
    /// number of atomic propositions never overlap.
    fn overlaps(&self, other: &Self) -> bool {
        self.num_aps == other.num_aps && self.bdd.and(&other.bdd).sat_witness().is_some()
    }
}

/// An iterator over the [`PropSymbol`]s that satisfy a [`PropExpression`].
pub struct PropExpressionSymbols<'a, RawTy: RawSymbolRepr> {
    iter: BddSatisfyingValuations<'a>,
    _ty: PhantomData<RawTy>,
}

impl<RawTy: RawSymbolRepr> Iterator for PropExpressionSymbols<'_, RawTy> {
    type Item = PropSymbol<RawTy>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(PropSymbol::from_bdd_valuation(self.iter.next()?))
    }
}

/// Represents a propositional alphabet, which consists of a list of atomic propositions.
///
/// A symbol of this alphabet simply a valuation of the atomic propositions, which is
/// represented as a binary string of length `num_aps` (whose limit gets determined by
/// the number of bits in the type parameter `RawTy`).
///
/// An Expression is represented by a boolean formula over the atomic propositions. Here,
/// we store it as a [`PropExpression`] which in turn contains a [`Bdd`].
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
    expressions: Arc<Mutex<BTreeSet<PropExpression<RawTy>>>>,
}

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
        Ok(Self {
            expressions: Arc::new(Mutex::new(BTreeSet::from_iter([universal.clone()]))),
            universal,
            aps,
        })
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
        let expr = PropExpression {
            bdd: Bdd::from(symbol.as_bdd_valuation()),
            num_aps: symbol.num_aps,
            _ty: PhantomData,
        };
        let mut expressions = self.expressions.lock().unwrap();
        expressions.insert(expr.clone());
        Some(expr)
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

    #[test]
    fn expressions_are_rendered_over_indices_for_hoa_and_letters_for_humans() {
        let both = PropExpression::<u32>::new(2, "x_0 & !x_1");
        assert_eq!(both.to_hoa_label(), "0 & !1");
        assert_eq!(both.show(), "a&!b");

        let either = PropExpression::<u32>::new(2, "x_0 | x_1");
        let label = either.to_hoa_label();
        assert!(label.contains(" | "), "{label}");
        assert!(
            !label.contains(|c: char| c.is_ascii_alphabetic()),
            "{label}"
        );

        let always = PropExpression::<u32>::universal(2);
        assert_eq!(always.to_hoa_label(), "t");
        let never = PropExpression::<u32>::new(2, "x_0 & !x_0");
        assert_eq!(never.to_hoa_label(), "f");
        assert_eq!(never.show(), "f");
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

    #[test]
    fn expression_overlaps() {
        let a_and_b = PropExpression::<u32>::new(2, "x_0 & x_1");
        let a = PropExpression::<u32>::new(2, "x_0");
        let not_a = PropExpression::<u32>::new(2, "!x_0");
        assert!(a_and_b.overlaps(&a));
        assert!(a.overlaps(&a_and_b));
        assert!(!a.overlaps(&not_a));
        // different numbers of atomic propositions never overlap
        assert!(!a.overlaps(&PropExpression::<u32>::new(3, "x_0")));
    }

    #[test]
    fn prop_symbol() {
        let ps = PropSymbol {
            num_aps: 5,
            raw: 19u32,
        };
        assert_eq!(ps.show(), "10011".to_string());
    }

    #[test]
    fn prop_expression() {
        let pe = PropExpression::<u32>::new(3, "x_0 | (x_1 & x_2)");

        assert!(PropSymbol::from_bools(vec![false, true, true]).matches(&pe));
        assert!(PropSymbol::from_bools(vec![false, true, true]).matches(&pe));
        assert!(!PropSymbol::from_bools(vec![false, false, false]).matches(&pe));
    }
}
