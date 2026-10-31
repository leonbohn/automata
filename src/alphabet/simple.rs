use std::collections::{BTreeSet, VecDeque};

use itertools::Itertools;

use crate::show::Show;

use super::{Alphabet, Expression, IndexedAlphabet, Matcher, Symbol};

/// An alphabet of individual symbols that are their own expressions, i.e. every edge is labeled
/// by a single symbol. The symbols are numbered in a fixed order.
pub trait SimpleAlphabet: Alphabet
where
    Self: Alphabet<Expression = <Self as Alphabet>::Symbol>,
{
    /// Returns the expression that matches exactly the given symbol.
    ///
    /// # Panics
    /// Panics if the symbol does not belong to the alphabet.
    fn express(&self, sym: Self::Symbol) -> &Self::Expression;
    /// Returns the `pos`-th symbol of the alphabet, or `None` if `pos` is out of range.
    fn try_nth(&self, pos: usize) -> Option<Self::Symbol>;
    /// Returns the `pos`-th symbol of the alphabet.
    ///
    /// # Panics
    ///
    /// Panics if `pos` is out of range, see [`Self::try_nth`].
    fn nth(&self, pos: usize) -> Self::Symbol {
        self.try_nth(pos).unwrap()
    }
    /// Returns the position of the given symbol in the alphabet, or `None` if it is not part of it.
    fn try_position(&self, symbol: Self::Symbol) -> Option<usize>;
    /// Returns the position of the given symbol in the alphabet.
    ///
    /// # Panics
    ///
    /// Panics if the symbol is not part of the alphabet, see [`Self::try_position`].
    fn position(&self, symbol: Self::Symbol) -> usize {
        self.try_position(symbol).unwrap()
    }
}

/// The symbols given for an alphabet do not fit its size, see [`FromSymbols::try_from_symbols`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("the alphabet has {expected} symbols but {found} were given")]
pub struct WrongAlphabetSize {
    /// The number of symbols of the alphabet.
    pub expected: usize,
    /// The number of distinct symbols that were given.
    pub found: usize,
}

/// A [`SimpleAlphabet`] that can be created from its set of symbols. This is what the
/// [`Builder`](crate::ts::Builder) uses to create the alphabet of the system it builds from the
/// symbols on the edges.
pub trait FromSymbols: SimpleAlphabet + Sized {
    /// Creates the alphabet with exactly the given symbols.
    ///
    /// # Errors
    /// Returns [`WrongAlphabetSize`] if the alphabet has a fixed size that differs from the number
    /// of symbols.
    fn try_from_symbols(symbols: BTreeSet<Self::Symbol>) -> Result<Self, WrongAlphabetSize>;
}

/// Represents an alphabet where a [`Symbol`] is just a single `char`.
///
/// # Example
/// Assume we have a [`CharAlphabet`] over the symbols 'a' and 'b'. Then a **symbol** would be just one of these
/// characters, e.g. 'a'. This is used to label transitions in a transition system or automaton.
/// Now an **expression** would also be just a single character, e.g. 'a'. Then such an expression is
/// matched by a symbol if the expression equals the symbol.
#[derive(Clone, Hash, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct CharAlphabet(pub(crate) Vec<char>);

impl CharAlphabet {
    /// Sorts and deduplicates the symbols, so that the position of a symbol can be found by binary
    /// search.
    fn from_symbols(mut symbols: Vec<char>) -> Self {
        symbols.sort_unstable();
        symbols.dedup();
        Self(symbols)
    }

    /// Creates a new [`CharAlphabet`] alphabet of the given size. The symbols are the first `size`
    /// letters of the alphabet, i.e. 'a' to 'z', followed by the characters after 'z' in code point
    /// order if `size` exceeds 26.
    ///
    /// # Panics
    ///
    /// Panics if the symbols would leave the range of valid characters.
    pub fn of_size(size: usize) -> Self {
        Self::from_symbols(
            (0..size)
                .map(|i| char::from_u32('a' as u32 + i as u32).expect("Alphabet is too large"))
                .collect(),
        )
    }
}

impl std::ops::Index<usize> for CharAlphabet {
    type Output = char;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl From<Vec<char>> for CharAlphabet {
    fn from(value: Vec<char>) -> Self {
        Self::from_symbols(value)
    }
}

impl FromIterator<char> for CharAlphabet {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        Self::from_symbols(iter.into_iter().collect())
    }
}

impl CharAlphabet {
    /// Creates a new [`CharAlphabet`] alphabet from an iterator over the symbols.
    pub fn new(symbols: Vec<char>) -> Self {
        Self::from_symbols(symbols)
    }
}

impl Matcher<char> for char {
    fn matches(&self, expression: &char) -> bool {
        self == expression
    }
}

impl Expression for char {
    type S = char;
    type SymbolsIter<'this>
        = std::iter::Once<char>
    where
        Self: 'this;
    fn symbols(&self) -> Self::SymbolsIter<'_> {
        std::iter::once(*self)
    }
    fn overlaps(&self, other: &Self) -> bool {
        self == other
    }

    fn for_each<F: Fn(char)>(&self, f: F) {
        (f)(*self)
    }

    fn matched_by(&self, symbol: char) -> bool {
        self == &symbol
    }
}

impl Alphabet for CharAlphabet {
    type Symbol = char;

    type Expression = char;

    type Universe<'this>
        = std::iter::Cloned<std::slice::Iter<'this, char>>
    where
        Self: 'this;

    fn size(&self) -> usize {
        self.0.len()
    }

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        left == right
    }

    fn universe(&self) -> Self::Universe<'_> {
        self.0.iter().cloned()
    }

    fn contains(&self, symbol: Self::Symbol) -> bool {
        self.0.binary_search(&symbol).is_ok()
    }

    #[inline(always)]
    fn search_edge<X>(
        map: &std::collections::BTreeMap<Self::Expression, X>,
        sym: Self::Symbol,
    ) -> Option<(&Self::Expression, &X)> {
        map.get_key_value(&sym)
    }

    fn try_make_expression(&self, symbol: Self::Symbol) -> Option<Self::Expression> {
        self.0.iter().find(|c| c == &&symbol).copied()
    }
}

impl SimpleAlphabet for CharAlphabet {
    fn express(&self, sym: Self::Symbol) -> &Self::Expression {
        self.0
            .iter()
            .find(|c| c == &&sym)
            .expect("cannot express unavailable symbol!")
    }

    fn try_nth(&self, pos: usize) -> Option<Self::Symbol> {
        self.0.get(pos).cloned()
    }

    fn try_position(&self, symbol: Self::Symbol) -> Option<usize> {
        self.0.binary_search(&symbol).ok()
    }
}

impl FromSymbols for CharAlphabet {
    fn try_from_symbols(symbols: BTreeSet<char>) -> Result<Self, WrongAlphabetSize> {
        Ok(Self(symbols.into_iter().collect()))
    }
}

impl IndexedAlphabet for CharAlphabet {
    #[inline]
    fn try_symbol_to_index(&self, sym: Self::Symbol) -> Option<usize> {
        self.0.binary_search(&sym).ok()
    }

    #[inline]
    fn expression_to_index(&self, sym: &Self::Expression) -> usize {
        self.symbol_to_index(*sym)
    }

    #[inline]
    fn symbol_from_index(&self, index: usize) -> Self::Symbol {
        self.0[index]
    }

    #[inline]
    fn expression_from_index(&self, index: usize) -> Self::Expression {
        self.symbol_from_index(index)
    }

    #[inline]
    fn expression_ref(&self, index: usize) -> &Self::Expression {
        &self.0[index]
    }
}

/// An alphabet of fixed arity, uses const generics. This is more seen as a test
/// since the performance gains (at least for simple operations like runs) is
/// negligible.
#[derive(Clone, Debug)]
pub struct Fixed<S: Symbol, const N: usize>([S; N]);

impl Matcher<usize> for usize {
    fn matches(&self, expression: &usize) -> bool {
        self == expression
    }
}

impl Expression for usize {
    type S = usize;
    type SymbolsIter<'this>
        = std::iter::Once<usize>
    where
        Self: 'this;

    fn symbols(&self) -> Self::SymbolsIter<'_> {
        std::iter::once(*self)
    }
    fn overlaps(&self, other: &Self) -> bool {
        self == other
    }

    fn matched_by(&self, symbol: usize) -> bool {
        *self == symbol
    }
}

impl<S: Symbol + Matcher<S> + Expression<S = S>, const N: usize> IndexedAlphabet for Fixed<S, N> {
    #[inline]
    fn try_symbol_to_index(&self, sym: Self::Symbol) -> Option<usize> {
        self.0.iter().position(|x| *x == sym)
    }

    #[inline]
    fn expression_to_index(&self, sym: &Self::Expression) -> usize {
        self.symbol_to_index(*sym)
    }

    #[inline]
    fn symbol_from_index(&self, index: usize) -> Self::Symbol {
        self.0[index]
    }

    #[inline]
    fn expression_from_index(&self, index: usize) -> Self::Expression {
        self.symbol_from_index(index)
    }

    #[inline]
    fn expression_ref(&self, index: usize) -> &Self::Expression {
        &self.0[index]
    }
}

impl<S: Symbol, const N: usize> Fixed<S, N> {
    /// Create a new [`Fixed`] alphabet from a slice of length `N`.
    pub fn from(symbols: [S; N]) -> Self {
        Self(symbols)
    }
}

impl<S: Symbol + Matcher<S> + Expression<S = S>, const N: usize> Alphabet for Fixed<S, N> {
    type Symbol = S;

    type Expression = S;

    fn search_edge<X>(
        map: &std::collections::BTreeMap<Self::Expression, X>,
        sym: Self::Symbol,
    ) -> Option<(&Self::Expression, &X)> {
        map.get_key_value(&sym)
    }

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        left == right
    }

    fn size(&self) -> usize {
        N
    }

    type Universe<'this>
        = std::iter::Cloned<std::slice::Iter<'this, S>>
    where
        Self: 'this;

    fn universe(&self) -> Self::Universe<'_> {
        self.0.iter().cloned()
    }

    fn contains(&self, symbol: Self::Symbol) -> bool {
        self.0.contains(&symbol)
    }

    fn try_make_expression(&self, symbol: Self::Symbol) -> Option<Self::Expression> {
        self.0.iter().find(|c| c == &&symbol).copied()
    }
}

impl<S: Symbol + Matcher<S> + Expression<S = S>, const N: usize> SimpleAlphabet for Fixed<S, N> {
    fn express(&self, sym: Self::Symbol) -> &Self::Expression {
        self.0
            .iter()
            .find(|c| c == &&sym)
            .expect("cannot express unavailable symbol!")
    }

    fn try_nth(&self, pos: usize) -> Option<Self::Symbol> {
        self.0.get(pos).copied()
    }

    fn try_position(&self, symbol: Self::Symbol) -> Option<usize> {
        self.0.iter().position(|c| *c == symbol)
    }
}

impl<S: Symbol + Matcher<S> + Expression<S = S>, const N: usize> FromSymbols for Fixed<S, N> {
    /// The symbols are put in ascending order.
    fn try_from_symbols(symbols: BTreeSet<S>) -> Result<Self, WrongAlphabetSize> {
        let found = symbols.len();
        <[S; N]>::try_from(symbols.into_iter().collect::<Vec<_>>())
            .map(Self)
            .map_err(|_| WrongAlphabetSize { expected: N, found })
    }
}

/// A [`CharAlphabet`] alphabet where symbols can be inverted. This means that a symbol can either be
/// appended to the end of a word or prepended to the beginning of a word. This is used to
/// implement the [`Directional`] alphabet.
#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct InvertibleChar(char, bool);

impl InvertibleChar {
    /// Multiplies the given word with this symbol. If the symbol is inverted, then it is prepended
    /// to the word, otherwise it is appended.
    pub fn mul(&self, word: &mut VecDeque<char>) {
        if self.1 {
            word.push_front(self.0)
        } else {
            word.push_back(self.0)
        }
    }

    /// Returns the underlying character.
    pub fn symbol(&self) -> char {
        self.0
    }

    /// Returns true if this symbol is inverted.
    pub fn is_inverted(&self) -> bool {
        self.1
    }
}

impl Matcher<InvertibleChar> for InvertibleChar {
    fn matches(&self, expression: &InvertibleChar) -> bool {
        self == expression
    }
}

impl Expression for InvertibleChar {
    type S = InvertibleChar;
    type SymbolsIter<'this>
        = std::iter::Once<InvertibleChar>
    where
        Self: 'this;

    fn symbols(&self) -> Self::SymbolsIter<'_> {
        std::iter::once(*self)
    }
    fn overlaps(&self, other: &Self) -> bool {
        self == other
    }

    fn matched_by(&self, symbol: InvertibleChar) -> bool {
        *self == symbol
    }
}

impl Show for InvertibleChar {
    fn show(&self) -> String {
        format!("{}{}", self.0, if self.1 { "\u{0303}" } else { "" })
    }

    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        format!("'{}'", iter.into_iter().rev().map(|c| c.show()).join(""))
    }
}

/// A [`CharAlphabet`] alphabet where each symbol can be inverted. This means that a symbol can either be
/// appended to the end of a word or prepended to the beginning of a word. This can be used to
/// represent two-sided congruences.
#[derive(Clone, Debug)]
pub struct Directional(Vec<InvertibleChar>);

impl FromIterator<char> for Directional {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let mut v = vec![];
        for sym in iter {
            v.push(InvertibleChar(sym, false));
            v.push(InvertibleChar(sym, true));
        }
        Self(v)
    }
}

impl Directional {
    /// Takes a 'usual' alphabet and turns every symbol into an [`InvertibleChar`], that is every
    /// char can now be an append- or a prepend-symbol.
    pub fn from_alphabet<A: std::borrow::Borrow<CharAlphabet>>(alphabet: A) -> Self {
        Self::from_iter(alphabet.borrow().universe())
    }
}

impl Alphabet for Directional {
    type Symbol = InvertibleChar;

    type Expression = InvertibleChar;

    fn search_edge<X>(
        map: &std::collections::BTreeMap<Self::Expression, X>,
        sym: Self::Symbol,
    ) -> Option<(&Self::Expression, &X)> {
        map.get_key_value(&sym)
    }

    fn size(&self) -> usize {
        self.0.len()
    }

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        left == right
    }

    type Universe<'this>
        = std::iter::Cloned<std::slice::Iter<'this, InvertibleChar>>
    where
        Self: 'this;

    fn universe(&self) -> Self::Universe<'_> {
        self.0.iter().cloned()
    }

    fn contains(&self, symbol: Self::Symbol) -> bool {
        self.0.contains(&symbol)
    }

    fn try_make_expression(&self, symbol: Self::Symbol) -> Option<Self::Expression> {
        self.0.iter().find(|c| c == &&symbol).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::{Alphabet, SimpleAlphabet};
    use super::{CharAlphabet, Directional, Fixed};
    use crate::alphabet::IndexedAlphabet;
    use itertools::Itertools;

    #[test]
    fn make_expression_rejects_foreign_symbols() {
        let alph = CharAlphabet::from_iter(['a', 'b']);
        assert_eq!(alph.try_make_expression('a'), Some('a'));
        assert_eq!(alph.try_make_expression('z'), None);
    }

    #[test]
    fn bialphabet() {
        let alph = CharAlphabet::from_iter(['a', 'b', 'c']);
        let bi = Directional::from_alphabet(alph);
        assert_eq!(bi.universe().collect_vec().len(), 6);
    }

    #[test]
    fn char_alphabet_is_sorted_and_deduplicated() {
        let alph = CharAlphabet::new(vec!['c', 'a', 'b', 'a']);
        assert_eq!(alph.universe().collect_vec(), vec!['a', 'b', 'c']);
        assert_eq!(alph, CharAlphabet::from(vec!['b', 'c', 'a']));
    }

    #[test]
    fn char_alphabet_of_size() {
        assert_eq!(
            CharAlphabet::of_size(3).universe().collect_vec(),
            vec!['a', 'b', 'c']
        );
        let large = CharAlphabet::of_size(40);
        assert_eq!(large.size(), 40);
        assert_eq!(large.symbol_from_index(39), (b'a' + 39) as char);
    }

    #[test]
    fn char_alphabet_indexing_round_trips() {
        for alph in [
            CharAlphabet::of_size(0),
            CharAlphabet::of_size(5),
            CharAlphabet::new(vec!['x', 'a', 'é', 'λ', '0']),
        ] {
            for (i, sym) in alph.universe().enumerate() {
                assert_eq!(alph.symbol_to_index(sym), i);
                assert_eq!(alph.expression_to_index(&sym), i);
                assert_eq!(alph.symbol_from_index(i), sym);
                assert_eq!(alph.expression_from_index(i), sym);
                assert_eq!(alph.expression_to_symbol(&sym), sym);
                assert_eq!(alph.symbol_to_expression(sym), sym);
                assert_eq!(alph.try_position(sym), Some(i));
                assert!(alph.contains(sym));
            }
        }
    }

    #[test]
    fn char_alphabet_absent_symbols() {
        let alph = CharAlphabet::of_size(3);
        assert!(!alph.contains('d'));
        assert_eq!(alph.try_position('d'), None);
    }

    #[test]
    #[should_panic(expected = "Must be present in alphabet")]
    fn char_alphabet_index_of_absent_symbol_panics() {
        CharAlphabet::of_size(3).symbol_to_index('z');
    }

    #[test]
    fn fixed_alphabet_indexing_follows_array_order() {
        let alph = Fixed::from([7usize, 2, 5]);
        for (i, sym) in [7usize, 2, 5].into_iter().enumerate() {
            assert_eq!(alph.symbol_to_index(sym), i);
            assert_eq!(alph.expression_to_index(&sym), i);
            assert_eq!(alph.symbol_from_index(i), sym);
            assert_eq!(alph.expression_from_index(i), sym);
        }
    }
}
