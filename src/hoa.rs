#![allow(missing_docs)]
pub mod input;
pub mod output;

use std::cell::RefCell;

use crate::prelude::*;
use biodivine_lib_bdd::{
    Bdd, BddPartialValuation, BddSatisfyingValuations, BddValuation, BddVariable,
};
use hoars::HoaAutomaton;
use itertools::Itertools;

use self::alphabet::Matcher;

pub static MAX_APS: usize = 6;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct HoaString(pub(crate) String);

/// A propositional alphabet, where a symbol is a valuation of all propositional variables.
///
/// # Example
/// Assume we have a propositional alphabet over the atomic propositions `a`, `b` and `c`.
///
/// Then a **symbol** in this alphabet is a valuation of these variables, e.g. `a & !b & c`. This is used to label
/// transitions in a [`crate::transition_system::TransitionSystem`].
///
/// An **expression** on the other hand is used to label edges and it is a boolean expression over
/// the atomic propositions, e.g. `(a | b) & c`. Such an expression is matched by
/// a symbol if the symbol satisfies the expression, i.e. if the expression evaluates to `true` under the given
/// valuation. The expression from above, for example, would be matched by the symbol given above (`a & !b & c`),
/// but not by the symbols `a & b & !c` or `!a & !b & c`.
#[derive(Clone)]
pub struct HoaAlphabet {
    apnames: Vec<String>,
    variable_set: biodivine_lib_bdd::BddVariableSet,
    variables: Vec<BddVariable>,
    // TODO: introduce caching of Bdds
    _expressions: RefCell<math::Set<HoaExpression>>,
}

impl HoaAlphabet {
    pub fn size(&self) -> usize {
        2u32.saturating_pow(self.apnames.len() as u32)
            .try_into()
            .expect("Cannot fit value into usize")
    }

    pub fn char_to_hoa_symbol(&self, value: char) -> HoaSymbol {
        assert!(value >= 'a');

        let repr = (value as u8) - b'a';
        HoaSymbol {
            repr,
            aps: self.apnames_len(),
        }
    }

    pub fn hoa_symbol_to_char(&self, sym: &HoaSymbol) -> char {
        assert_eq!(
            sym.aps,
            self.apnames_len(),
            "symbol does not match alphabet"
        );
        assert!(sym.aps <= MAX_APS, "Too many APs");

        (b'a' + sym.repr) as char
    }

    pub fn apnames(&self) -> &[String] {
        &self.apnames
    }
    pub fn apnames_len(&self) -> usize {
        self.apnames.len()
    }

    /// Attempts to build an instance of `Self` from the given pointer to a [`CharAlphabet`]. This
    /// only works (for the moment) if the number of symbols in the given alphabet is an exact
    /// power of two.
    pub fn try_from_char_alphabet(value: &CharAlphabet) -> Result<Self, String> {
        let alphabet_size = value.size();
        if alphabet_size != alphabet_size.next_power_of_two() || alphabet_size == 0 {
            return Err(format!(
                "Alphabet size is not a power of two: {alphabet_size}"
            ));
        }

        let aps = alphabet_size.ilog2() as u8;
        assert!(aps > 0, "We do not want this edge case");

        Ok(Self::from_apnames(
            (0u8..aps).map(|i| ((b'a' + i) as char).to_string()),
        ))
    }

    pub fn from_apnames<I: IntoIterator<Item = String>>(apnames: I) -> Self {
        let apnames: Vec<_> = apnames.into_iter().collect();
        assert!(apnames.len() < MAX_APS);
        assert!(!apnames.is_empty());

        let (vs, vars) = hoars::build_vars(apnames.len() as u16);

        Self {
            apnames,
            variable_set: vs,
            variables: vars,
            _expressions: RefCell::new(math::Set::default()),
        }
    }

    pub fn from_hoa_automaton(aut: &HoaAutomaton) -> Self {
        Self::from_apnames(aut.aps().clone())
    }
    pub fn top(&self) -> Bdd {
        self.variable_set.mk_true()
    }
    pub fn bot(&self) -> Bdd {
        self.variable_set.mk_false()
    }
    pub fn var(&self, n: usize) -> Bdd {
        self.variable_set.mk_var(self.nth_variable(n))
    }
    pub fn not_var(&self, n: usize) -> Bdd {
        self.variable_set.mk_not_var(self.nth_variable(n))
    }
    pub fn nth_variable(&self, n: usize) -> BddVariable {
        assert!(n < MAX_APS);
        assert!(n < self.apnames.len());
        self.variables[n]
    }
}

pub(crate) fn hoa_symbol_to_hoa_expression(symbol: &HoaSymbol) -> HoaExpression {
    let bdd: Bdd = symbol.as_bdd_valuation().into();
    HoaExpression {
        bdd,
        aps: symbol.aps,
    }
}

pub(crate) fn bdd_valuation_to_hoa_symbol(valuation: &BddValuation) -> HoaSymbol {
    let aps: usize = valuation.num_vars().into();
    assert!(
        aps <= MAX_APS,
        "We have {aps}, which is more than the maximum of {MAX_APS}"
    );
    let mut repr = 0;
    for (var, b) in valuation.to_values() {
        if b {
            repr |= 1 << var.to_index()
        }
    }
    HoaSymbol { repr, aps }
}
#[derive(Debug, Clone, Eq, PartialEq, Hash, Copy)]
pub struct HoaSymbol {
    repr: u8,
    aps: usize,
}

impl HoaSymbol {
    fn as_bdd_valuation(&self) -> BddValuation {
        let mut valuation = BddValuation::all_false(self.aps.try_into().unwrap());
        for i in 0..self.aps {
            let val = ((1 << i) & self.repr) > 0;
            valuation.set_value(BddVariable::from_index(i), val);
        }

        assert_eq!(valuation.num_vars() as usize, self.aps);
        valuation
    }
    pub fn to_char(&self) -> char {
        assert!(self.aps <= MAX_APS, "Too many APs");
        (b'a' + (self.repr & 0b1111)) as char
    }
    pub fn from_char(value: char, aps: usize) -> Self {
        assert!(aps <= MAX_APS);
        let val = value as u8;
        assert!(b'a' < val);
        assert!(val <= b'p');

        Self {
            repr: (val - b'a') & 0b1111,
            aps,
        }
    }
}

impl PartialOrd for HoaSymbol {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for HoaSymbol {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.aps.cmp(&other.aps).then(self.repr.cmp(&other.repr))
    }
}
impl Show for HoaSymbol {
    fn show(&self) -> String {
        (0..self.aps)
            .map(|i| {
                if ((1 << i) & self.repr) > 0 {
                    i.to_string()
                } else {
                    format!("!{i}")
                }
            })
            .join(" & ")
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct HoaExpression {
    bdd: Bdd,
    aps: usize,
}

impl Matcher<HoaExpression> for HoaExpression {
    fn matches(&self, _expression: &HoaExpression) -> bool {
        todo!()
    }
}

impl HoaExpression {
    pub fn new(bdd: Bdd, aps: usize) -> Self {
        Self { bdd, aps }
    }

    pub fn chars_iter(&self) -> impl Iterator<Item = char> + '_ {
        self.symbols().map(|a| a.to_char())
    }

    pub fn aps(&self) -> usize {
        self.aps
    }
}

impl std::ops::BitAnd for HoaExpression {
    type Output = HoaExpression;

    fn bitand(self, rhs: Self) -> Self::Output {
        assert_eq!(self.aps, rhs.aps);
        HoaExpression {
            aps: self.aps,
            bdd: self.bdd.and(&rhs.bdd),
        }
    }
}

impl std::ops::Not for HoaExpression {
    type Output = HoaExpression;

    fn not(self) -> Self::Output {
        HoaExpression {
            aps: self.aps,
            bdd: self.bdd.not(),
        }
    }
}

impl std::ops::BitOr for HoaExpression {
    type Output = HoaExpression;
    fn bitor(self, rhs: Self) -> Self::Output {
        HoaExpression {
            aps: self.aps,
            bdd: self.bdd.or(&rhs.bdd),
        }
    }
}

impl std::ops::BitAndAssign for HoaExpression {
    fn bitand_assign(&mut self, rhs: Self) {
        assert_eq!(self.aps, rhs.aps);
        self.bdd = self.bdd.and(&rhs.bdd);
    }
}

impl std::ops::BitOrAssign for HoaExpression {
    fn bitor_assign(&mut self, rhs: Self) {
        assert_eq!(self.aps, rhs.aps);
        self.bdd = self.bdd.or(&rhs.bdd);
    }
}
impl PartialOrd for HoaExpression {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for HoaExpression {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.aps
            .cmp(&other.aps)
            .then(self.bdd.sat_witness().cmp(&other.bdd.sat_witness()))
    }
}
impl Show for HoaExpression {
    fn show(&self) -> String {
        let convert_clause = |clause: BddPartialValuation| {
            if clause.is_empty() {
                return "t".to_string();
            }
            clause
                .to_values()
                .into_iter()
                .map(|(var, b)| {
                    if b {
                        var.to_index().to_string()
                    } else {
                        format!("!{}", var.to_index())
                    }
                })
                .join(" & ")
        };

        let dnf = self.bdd.to_dnf();

        if dnf.is_empty() {
            panic!("Decide on how to deal with this!");
        }

        if dnf.len() == 1 {
            return convert_clause(dnf.into_iter().next().expect("length is 1"));
        }

        dnf.into_iter()
            .map(|clause| format!("({})", convert_clause(clause)))
            .join(" | ")
    }
}

pub struct HoaExpressionIter<'a> {
    iter: BddSatisfyingValuations<'a>,
}

impl<'a> HoaExpressionIter<'a> {
    pub fn new(expr: &'a HoaExpression) -> Self {
        Self {
            iter: expr.bdd.sat_valuations(),
        }
    }
}

impl<'a> Iterator for HoaExpressionIter<'a> {
    type Item = HoaSymbol;
    fn next(&mut self) -> Option<Self::Item> {
        let val = self.iter.next()?;
        Some(bdd_valuation_to_hoa_symbol(&val))
    }
}

impl Matcher<HoaExpression> for HoaSymbol {
    fn matches(&self, expression: &HoaExpression) -> bool {
        expression.matched_by(*self)
    }
}

impl Expression for HoaExpression {
    type S = HoaSymbol;
    type SymbolsIter<'this> = HoaExpressionIter<'this> where Self: 'this;

    fn overlaps(&self, other: &Self) -> bool {
        self.bdd.and(&other.bdd).sat_valuations().next().is_some()
    }

    fn symbols(&self) -> Self::SymbolsIter<'_> {
        HoaExpressionIter::new(self)
    }

    fn matched_by(&self, symbol: HoaSymbol) -> bool {
        self.bdd.eval_in(&symbol.as_bdd_valuation())
    }
}

pub struct HoaUniverse {
    aps: u8,
    current: u8,
}

impl Iterator for HoaUniverse {
    type Item = HoaSymbol;
    fn next(&mut self) -> Option<Self::Item> {
        if (self.current as u16) < (2u32.saturating_pow(self.aps as u32) as u16) {
            let out = self.current;
            self.current += 1;
            Some(HoaSymbol {
                repr: out,
                aps: (self.aps as usize),
            })
        } else {
            None
        }
    }
}

impl HoaUniverse {
    pub fn new(aps: usize) -> Self {
        assert!(aps <= MAX_APS);
        Self {
            aps: aps.try_into().unwrap(),
            current: 0,
        }
    }
}

impl Alphabet for HoaAlphabet {
    type Symbol = HoaSymbol;

    type Expression = HoaExpression;

    fn size(&self) -> usize {
        2u32.saturating_pow(self.apnames.len() as u32)
            .try_into()
            .expect("Cannot fit value into usize")
    }

    type Universe<'this> = HoaUniverse
    where
        Self: 'this;

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        left.bdd.and(&right.bdd).sat_valuations().next().is_some()
    }

    fn universe(&self) -> Self::Universe<'_> {
        let aps = self.apnames.len();
        assert!(aps <= MAX_APS);
        HoaUniverse::new(self.apnames.len())
    }

    fn contains(&self, symbol: Self::Symbol) -> bool {
        for i in (0..MAX_APS).rev() {
            if (symbol.repr & (1 << i)) > 0 {
                return i < self.apnames.len();
            }
        }
        true
    }

    fn make_expression(&self, symbol: Self::Symbol) -> Self::Expression {
        hoa_symbol_to_hoa_expression(&symbol)
    }
}

impl std::fmt::Debug for HoaAlphabet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Propositional[{}]", self.apnames().join(", "))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        hoa::{input::hoa_to_ts, HoaAlphabet},
        TransitionSystem,
    };

    #[test_log::test]
    fn parse_generated_hoa() {
        let hoa = r#"HOA: v1
        States: 10
        Start: 0
        AP: 3 "2" "a" "b"
        acc-name: parity min even 5
        Acceptance: 5 Inf(0) | (Fin(1) & (Inf(2) | (Fin(3) & Inf(4))))
        properties: trans-labels explicit-labels trans-acc complete
        properties: deterministic
        --BODY--
        State: 0
        [0&1] 4
        [0&!1] 8
        [!0] 6 {0}
        State: 1
        [!0&1&2] 7 {0}
        [!0&1&!2] 3 {4}
        [!0&!1&2] 4 {0 4}
        [!0&!1&!2] 9 {0}
        [0] 5 {0 4}
        State: 2
        [0&1&2] 2 {0 4}
        [0&1&!2] 6 {3}
        [0&!1&2] 1 {1}
        [0&!1&!2] 4 {1}
        [!0] 7
        State: 3
        [0&1] 0 {2}
        [0&!1] 2
        [!0&1] 4 {3 4}
        [!0&!1] 6 {1 2}
        State: 4
        [0&1] 0 {3}
        [0&!1] 6 {1}
        [!0&1] 7 {0}
        [!0&!1] 4
        State: 5
        [0&1] 9
        [0&!1] 2
        [!0] 4
        State: 6
        [0&1] 9 {4}
        [0&!1] 0 {2}
        [!0&1] 6 {2 3}
        [!0&!1] 4 {0}
        State: 7
        [0&!1&2] 8 {4}
        [0&!1&!2] 1 {4}
        [0&1] 2 {1}
        [!0] 4 {2}
        State: 8
        [!0&1] 2
        [!0&!1] 6
        [0] 4
        State: 9
        [0] 5
        [!0] 3
        --END--
        "#;
        let start = std::time::Instant::now();
        let auts = hoa_to_ts(hoa);
        println!("Took {}ms", start.elapsed().as_millis());
        assert_eq!(auts.len(), 1);
        let aut = &auts[0];
        assert_eq!(aut.size(), 10);
    }

    #[test]
    fn hoa_symbol_char_conversion() {
        let alphabet =
            HoaAlphabet::from_apnames(["P0".to_string(), "P1".to_string(), "P2".to_string()]);

        for chr in 'a'..='e' {
            assert_eq!(
                chr,
                alphabet.hoa_symbol_to_char(&alphabet.char_to_hoa_symbol(chr))
            );
        }
    }
}
