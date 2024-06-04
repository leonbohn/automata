use std::{hash::Hash, marker::PhantomData};

use biodivine_lib_bdd::{Bdd, BddSatisfyingValuations, BddValuation, BddVariableSet, IntoBdd};
use tracing::trace;

use crate::prelude::*;

pub trait RawSymbolRepr: std::fmt::Debug + Hash + Eq + Ord + Copy {
    fn as_usize(&self) -> usize;
    fn from_usize(from: usize) -> Self;
    fn bit(&self, n: usize) -> bool;
    fn set(&mut self, n: usize);
}
impl RawSymbolRepr for u32 {
    fn as_usize(&self) -> usize {
        *self as usize
    }
    fn from_usize(from: usize) -> Self {
        from.try_into().unwrap()
    }
    fn bit(&self, n: usize) -> bool {
        assert!(n <= 8usize.saturating_pow(std::mem::size_of::<Self>() as u32));
        *self & (1 << n) != 0
    }
    fn set(&mut self, n: usize) {
        assert!(n <= 8usize.saturating_pow(std::mem::size_of::<Self>() as u32));
        *self |= 1 << n;
    }
}

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct PropSymbol<RawTy: RawSymbolRepr = u32> {
    num_aps: u8,
    raw: RawTy,
}

impl<RawTy: RawSymbolRepr> PropSymbol<RawTy> {
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
    pub fn as_bdd_valuation(&self) -> BddValuation {
        BddValuation::new(self.as_bools())
    }
    pub fn from_bdd_valuation(val: BddValuation) -> Self {
        Self::from_bools(val.vector())
    }
}

impl<RawTy: RawSymbolRepr> Show for PropSymbol<RawTy> {
    fn show(&self) -> String {
        let chr = |b| {
            if b {
                '1'
            } else {
                '0'
            }
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct PropExpression<RawTy: RawSymbolRepr = u32> {
    num_aps: u8,
    bdd: Bdd,
    _ty: PhantomData<RawTy>,
}

impl PropExpression<u32> {
    pub fn new(num_aps: u8, string: &str) -> Self {
        let vars = BddVariableSet::new_anonymous(num_aps as u16);
        Self {
            num_aps,
            bdd: vars.eval_expression_string(string),
            _ty: PhantomData,
        }
    }
    pub fn universal(num_aps: u8) -> Self {
        let vars = BddVariableSet::new_anonymous(num_aps as u16);
        Self {
            num_aps,
            bdd: vars.mk_true(),
            _ty: PhantomData,
        }
    }
    pub fn sat_vals(&self) -> PropExpressionSymbols<'_, u32> {
        PropExpressionSymbols {
            iter: self.bdd.sat_valuations(),
            _ty: PhantomData,
        }
    }
}

impl<RawTy: RawSymbolRepr> PartialOrd for PropExpression<RawTy> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        assert_eq!(self.num_aps, other.num_aps);
        Some(self.cmp(&other))
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

impl<RawTy: RawSymbolRepr> Show for PropExpression<RawTy> {
    fn show(&self) -> String {
        format!("{} aps: {}", self.num_aps, self.bdd)
    }
}

impl<RawTy: RawSymbolRepr> Matcher<PropExpression<RawTy>> for PropSymbol<RawTy> {
    fn matches(&self, expression: &PropExpression<RawTy>) -> bool {
        assert_eq!(self.num_aps, expression.num_aps);
        expression.bdd.eval_in(&self.as_bdd_valuation())
    }
}

impl<RawTy: RawSymbolRepr> Matcher<PropExpression<RawTy>> for PropExpression<RawTy> {
    fn matches(&self, _expression: &PropExpression<RawTy>) -> bool {
        todo!()
    }
}

impl<RawTy: RawSymbolRepr> Expression for PropExpression<RawTy> {
    type S = PropSymbol<RawTy>;

    type SymbolsIter<'this> = PropExpressionSymbols<'this, RawTy>
    where
        Self: 'this;

    fn symbols(&self) -> Self::SymbolsIter<'_> {
        PropExpressionSymbols {
            iter: self.bdd.sat_valuations(),
            _ty: PhantomData::<RawTy>,
        }
    }

    fn overlaps(&self, _other: &Self) -> bool {
        todo!()
    }
}

pub struct PropExpressionSymbols<'a, RawTy: RawSymbolRepr> {
    iter: BddSatisfyingValuations<'a>,
    _ty: PhantomData<RawTy>,
}

impl<'a, RawTy: RawSymbolRepr> Iterator for PropExpressionSymbols<'a, RawTy> {
    type Item = PropSymbol<RawTy>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(PropSymbol::from_bdd_valuation(self.iter.next()?))
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PropCache {
    aps: Vec<String>,
    universal: PropExpression,
    expressions: std::cell::RefCell<math::Set<PropExpression>>,
}

impl PropCache {
    pub fn new(aps: Vec<String>) -> Self {
        Self {
            universal: PropExpression::universal(aps.len() as u8),
            expressions: [].into_iter().collect::<math::Set<_>>().into(),
            aps,
        }
    }
}

impl Alphabet for PropCache {
    type Symbol = PropSymbol;

    type Expression = PropExpression;

    fn make_expression(&self, symbol: Self::Symbol) -> Self::Expression {
        let expr = PropExpression {
            bdd: Bdd::from(symbol.as_bdd_valuation()),
            num_aps: symbol.num_aps,
            _ty: PhantomData,
        };
        self.expressions.borrow_mut().insert(expr.clone());
        expr
    }

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        assert_eq!(left.num_aps, right.num_aps);
        left.bdd.and(&right.bdd).sat_witness().is_some()
    }

    type Universe<'this> = PropExpressionSymbols<'this, u32>
    where
        Self: 'this;

    fn universe(&self) -> Self::Universe<'_> {
        self.universal.sat_vals()
    }

    fn contains(&self, _symbol: Self::Symbol) -> bool {
        unimplemented!()
    }

    fn size(&self) -> usize {
        2usize.saturating_pow(self.aps.len() as u32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prop_symbol() {
        let ps = PropSymbol {
            num_aps: 5,
            raw: 19u32,
        };
        assert_eq!(ps.show(), "10011".to_string());
    }

    #[test_log::test]
    fn prop_expression() {
        let pe = PropExpression::new(3, "x_0 | (x_1 & x_2)");

        assert!(PropSymbol::from_bools(vec![false, true, true]).matches(&pe));
        assert!(PropSymbol::from_bools(vec![false, true, true]).matches(&pe));
        assert!(!PropSymbol::from_bools(vec![false, false, false]).matches(&pe));
    }
}
