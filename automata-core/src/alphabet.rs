use std::{fmt::Debug, hash::Hash};

use crate::prelude::*;

mod simple;
pub use simple::*;

mod propositional;
pub use propositional::*;

/// A symbol of an alphabet, which is also the type of the symbols in a word. We consider different types
/// of alphabets:
/// - [`CharAlphabet`] alphabets, which are just a set of symbols.
/// - Propositional alphabets, where a symbol is a valuation of all propositional variables. This is for example
/// implemented in the `hoars` crate.
pub trait Symbol: PartialEq + Eq + Debug + Copy + Ord + PartialOrd + Hash + Show {}
impl<S: PartialEq + Eq + Debug + Copy + Ord + PartialOrd + Hash + Show> Symbol for S {}

/// Encapsulates that an [`Expression`] can be matched by some [`Symbol`], or by another expression.
/// For simple [`CharAlphabet`]s, where expressions are single symbols, this is just equality.
pub trait Matcher<E>: Debug {
    /// Returns if `self` matches the given expression.
    fn matches(&self, expression: &E) -> bool;
}

impl<E, M: Matcher<E>> Matcher<E> for &M {
    fn matches(&self, expression: &E) -> bool {
        M::matches(*self, expression)
    }
}

/// An expression is used to label edges of a transition system/automaton. For [`CharAlphabet`]
/// alphabets, an expression is simply a single symbol, whereas for a propositional alphabet, an expression
/// is a propositional formula over the atomic propositions. See propositional for more details.
pub trait Expression: Hash + Clone + Debug + Eq + Ord + Show + Matcher<Self> {
    /// The type of symbols that this expression matches.
    type S: Symbol + Matcher<Self>;
    /// Type of iterator over the concrete symbols matched by this expression.
    type SymbolsIter<'this>: Iterator<Item = Self::S>
    where
        Self: 'this;
    /// Returns an iterator over the [`Symbol`]s that match this expression.
    fn symbols(&self) -> Self::SymbolsIter<'_>;

    /// Verifies whether or not this expression overlaps with the given expression. For a [`CharAlphabet`]
    /// alphabet, this just means that the two expressions are equal. For a propositional alphabet, this
    /// means that the two expressions share a common satisfying valuation.
    fn overlaps(&self, other: &Self) -> bool;

    /// Checks whether the given [`Symbol`] matches the expression `self`. For [`CharAlphabet`] alphabets, this just
    /// means that the expression equals the given symbol. For a propositional alphabet, this means that
    /// the expression is satisfied by the given symbol, an example of this is illustrated in propositional.
    fn matched_by(&self, symbol: Self::S) -> bool {
        symbol.matches(self)
    }

    /// Apply the given function `f` to each symbol matched by this expression.
    fn for_each<F: Fn(Self::S)>(&self, f: F) {
        self.symbols().for_each(f)
    }
}

pub trait SimpleAlphabet: Alphabet
where
    Self: Alphabet<Expression = <Self as Alphabet>::Symbol>,
{
    fn express(&self, sym: Self::Symbol) -> &Self::Expression;
}

/// An alphabet abstracts a collection of [`Symbol`]s and complex [`Expression`]s over those.
pub trait Alphabet: Clone + Debug {
    /// The type of symbols in this alphabet.
    type Symbol: Symbol + Matcher<Self::Expression>;
    /// The type of expressions in this alphabet.
    type Expression: Expression<S = Self::Symbol>;

    /// Creates an expression from a single symbol.
    fn make_expression(&self, symbol: Self::Symbol) -> Self::Expression;

    /// Returns a map from each symbol in the alphabet to the corresponding expression.
    fn expression_map(&self) -> math::Map<Self::Symbol, Self::Expression> {
        self.universe()
            .map(|sym| (sym, self.make_expression(sym)))
            .collect()
    }

    /// Returns true if the two expressions are disjoint, meaning they share no common valuations.
    fn disjoint(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        !self.overlapping(left, right)
    }

    /// Returns true if there exists a valuation/symbol matched by both expressions.
    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool;

    /// This method is used for an optimization: If we have a [`CharAlphabet`] alphabet, then an edge list essentially
    /// boils down to a map from `Self::Symbol` to an edge. For more complicated alphabets, this may not always
    /// be so easy. To allow for an optimization (i.e. just lookup the corresponding edge in a [`math::Map`]),
    /// we force alphabets to implement this method.
    fn search_edge<X>(
        map: &math::Map<Self::Expression, X>,
        sym: Self::Symbol,
    ) -> Option<(&Self::Expression, &X)> {
        map.iter().find_map(|(e, x)| {
            if e.matched_by(sym) {
                Some((e, x))
            } else {
                None
            }
        })
    }

    /// Type for an iterator over all possible symbols in the alphabet. For propositional alphabets,
    /// this may return quite a few symbols (exponential in the number of atomic propositions).
    type Universe<'this>: Iterator<Item = Self::Symbol>
    where
        Self: 'this;

    /// Returns an iterator over all possible symbols in the alphabet. May return a huge number of symbols
    /// if the alphabet is propositional.
    fn universe(&self) -> Self::Universe<'_>;

    /// Returns true if the given symbol is present in the alphabet.
    fn contains(&self, symbol: Self::Symbol) -> bool;

    /// Returns the number of symbols in the alphabet.
    fn size(&self) -> usize;

    fn is_empty(&self) -> bool {
        self.size() == 0
    }
}

impl<A: Alphabet> Alphabet for &A {
    type Expression = A::Expression;
    type Symbol = A::Symbol;
    type Universe<'this> = A::Universe<'this> where Self: 'this;
    fn universe(&self) -> Self::Universe<'_> {
        A::universe(self)
    }
    fn make_expression(&self, symbol: Self::Symbol) -> Self::Expression {
        A::make_expression(self, symbol)
    }
    fn search_edge<X>(
        map: &math::Map<Self::Expression, X>,
        sym: Self::Symbol,
    ) -> Option<(&Self::Expression, &X)> {
        A::search_edge(map, sym)
    }
    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        A::overlapping(self, left, right)
    }
    fn contains(&self, symbol: Self::Symbol) -> bool {
        A::contains(self, symbol)
    }
    fn size(&self) -> usize {
        A::size(self)
    }
}
