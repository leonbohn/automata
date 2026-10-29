use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{EdgeExpression, EdgeOf, EdgeRef, IdType, StateIndex, SymbolOf};
use crate::{Pointed, TransitionSystem};
use crate::{Show, alphabet::Alphabet};
use itertools::Itertools;
use std::borrow::Cow;

/// Trait that abstracts the product operation for transition systems.
pub trait Product: TransitionSystem + Sized {
    /// The type of output that is produced by the product operation.
    type Output<Ts: TransitionSystem<Alphabet = Self::Alphabet>>: TransitionSystem<Alphabet = Self::Alphabet, StateColor = (Self::StateColor, Ts::StateColor)>;
    /// Perform a product operation on two transition systems.
    fn ts_product<Ts: TransitionSystem<Alphabet = Self::Alphabet>>(
        self,
        other: Ts,
    ) -> Self::Output<Ts>;
}

impl<Lts: TransitionSystem + Sized> Product for Lts {
    type Output<Ts: TransitionSystem<Alphabet = Self::Alphabet>> = MatchingProduct<Self, Ts>;

    fn ts_product<Ts: TransitionSystem<Alphabet = Self::Alphabet>>(
        self,
        other: Ts,
    ) -> Self::Output<Ts> {
        MatchingProduct(self, other)
    }
}

/// Index type for product transition systems.
#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProductIndex<L, R>(pub L, pub R);

impl<L: IdType, R: IdType> IdType for ProductIndex<L, R> {}

impl<L, R> From<ProductIndex<L, R>> for (L, R) {
    fn from(value: ProductIndex<L, R>) -> Self {
        (value.0, value.1)
    }
}

impl<L: Show, R: Show> Show for ProductIndex<L, R> {
    fn show(&self) -> String {
        format!("({} | {})", self.0.show(), self.1.show())
    }

    fn show_collection<'a, I>(iter: I) -> String
    where
        Self: 'a,
        I: IntoIterator<Item = &'a Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        format!("{{{}}}", iter.into_iter().map(|x| x.show()).join(", "))
    }
}

impl<L: std::fmt::Display, R: std::fmt::Display> std::fmt::Display for ProductIndex<L, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.0, self.1)
    }
}

/// A product of two transition systems, which only permits transitions on matching symbols, while
/// ignoring all others.
#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MatchingProduct<L, R>(pub L, pub R);

impl<L, R> TransitionSystem for MatchingProduct<L, R>
where
    L: TransitionSystem,
    R: TransitionSystem,
    R::Alphabet: Alphabet<Symbol = SymbolOf<L>, Expression = EdgeExpression<L>>,
    L::StateColor: Clone,
    R::StateColor: Clone,
{
    type StateIndex = ProductIndex<L::StateIndex, R::StateIndex>;

    type EdgeColor = (L::EdgeColor, R::EdgeColor);

    type StateColor = (L::StateColor, R::StateColor);

    type EdgesFromIter<'this>
        = ProductEdgesFrom<'this, L, R>
    where
        Self: 'this;

    type Alphabet = L::Alphabet;

    fn alphabet(&self) -> &Self::Alphabet {
        self.0.alphabet()
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        let ProductIndex(l, r) = state;
        let left = self.0.state_color(l)?;
        let right = self.1.state_color(r)?;
        Some(Cow::Owned((left.into_owned(), right.into_owned())))
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        ProductEdges::new(&self.0, &self.1, state)
    }
}

impl<L, R> Pointed for MatchingProduct<L, R>
where
    L: Pointed,
    R: Pointed<Alphabet = L::Alphabet>,
{
    fn initial(&self) -> Self::StateIndex {
        ProductIndex(self.0.initial(), self.1.initial())
    }
}

/// Iterator over the edges of a product transition system, for successors and for predecessors.
/// For each edge of the left system, the edges of the right system at the right state are
/// iterated again (by asking the right system for a fresh iterator) instead of being collected
/// into a `Vec`, so no allocation takes place.
pub struct ProductEdges<'a, L: TransitionSystem, R: TransitionSystem, IL, IR> {
    left_edges: IL,
    current: Option<EdgeOf<'a, L>>,
    right: &'a R,
    right_state: R::StateIndex,
    start_right: fn(&'a R, R::StateIndex) -> Option<IR>,
    right_edges: Option<IR>,
}

/// Iterator over the edges of a product transition system that start in a state.
pub type ProductEdgesFrom<'a, L, R> = ProductEdges<
    'a,
    L,
    R,
    <L as TransitionSystem>::EdgesFromIter<'a>,
    <R as TransitionSystem>::EdgesFromIter<'a>,
>;

/// Iterator over the predecessors of a product transition system.
pub type ProductEdgesTo<'a, L, R> = ProductEdges<
    'a,
    L,
    R,
    <L as PredecessorIterable>::EdgesToIter<'a>,
    <R as PredecessorIterable>::EdgesToIter<'a>,
>;

impl<'a, L: TransitionSystem, R: TransitionSystem>
    ProductEdges<'a, L, R, L::EdgesFromIter<'a>, R::EdgesFromIter<'a>>
{
    /// Creates an iterator over the edges of the product that start in the state `(left, right)`.
    pub fn new(
        left: &'a L,
        right: &'a R,
        index: ProductIndex<L::StateIndex, R::StateIndex>,
    ) -> Option<Self> {
        right.edges_from(index.1)?.next();
        Some(Self {
            left_edges: left.edges_from(index.0)?,
            current: None,
            right,
            right_state: index.1,
            start_right: |right, state| right.edges_from(state),
            right_edges: None,
        })
    }
}

impl<'a, L: PredecessorIterable, R: PredecessorIterable>
    ProductEdges<'a, L, R, L::EdgesToIter<'a>, R::EdgesToIter<'a>>
{
    /// Creates an iterator over the edges of the product that lead to the state `(left, right)`.
    pub fn new_to(
        left: &'a L,
        right: &'a R,
        index: ProductIndex<L::StateIndex, R::StateIndex>,
    ) -> Option<Self> {
        right.predecessors(index.1)?.next();
        Some(Self {
            left_edges: left.predecessors(index.0)?,
            current: None,
            right,
            right_state: index.1,
            start_right: |right, state| right.predecessors(state),
            right_edges: None,
        })
    }
}

impl<'a, L, R, IL, IR> Iterator for ProductEdges<'a, L, R, IL, IR>
where
    L: TransitionSystem,
    R: TransitionSystem,
    R::Alphabet: Alphabet<Symbol = SymbolOf<L>, Expression = EdgeExpression<L>>,
    IL: Iterator<Item = EdgeOf<'a, L>>,
    IR: Iterator<Item = EdgeOf<'a, R>>,
{
    type Item = EdgeRef<
        'a,
        ProductIndex<L::StateIndex, R::StateIndex>,
        EdgeExpression<L>,
        (L::EdgeColor, R::EdgeColor),
    >;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.right_edges.is_none() {
                self.current = Some(self.left_edges.next()?);
                self.right_edges = (self.start_right)(self.right, self.right_state);
            }
            let left = self.current.as_ref()?;
            for right in self.right_edges.as_mut()?.by_ref() {
                if left.expression() == right.expression() {
                    return Some(EdgeRef::owned(
                        ProductIndex(left.source(), right.source()),
                        left.expression(),
                        (left.color().clone(), right.color().clone()),
                        ProductIndex(left.target(), right.target()),
                    ));
                }
            }
            self.right_edges = None;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::DTS;
    use crate::Void;
    use crate::automaton::MealyMachine;
    use crate::ts::Deterministic;
    use crate::ts::operations::{Product, ProductIndex};

    #[test]
    fn product_subalphabet() {
        let l: MealyMachine = DTS::builder()
            .default_color(Void)
            .with_transitions([(0, 'a', 0, 0), (0, 'b', 0, 0)])
            .into_mealy(0);
        let r: MealyMachine = DTS::builder()
            .default_color(Void)
            .with_transitions([(0, 'a', 0, 0)])
            .into_mealy(0);
        assert!((&l).ts_product(&l).reached_state("b").is_some());
        let prod = l.ts_product(r);
        assert!(prod.reached_state("a").is_some());
        assert!(prod.reached_state("b").is_none());
    }

    #[test]
    fn product_iterates_edges() {
        use crate::TransitionSystem;
        use crate::ts::Deterministic;
        let l: MealyMachine = DTS::builder()
            .default_color(Void)
            .with_transitions([
                (0, 'a', 0, 1),
                (0, 'b', 0, 0),
                (1, 'a', 1, 0),
                (1, 'b', 1, 1),
            ])
            .into_mealy(0);
        let r: MealyMachine = DTS::builder()
            .default_color(Void)
            .with_transitions([(0, 'a', 0, 0), (0, 'b', 0, 0)])
            .into_mealy(0);
        let prod = (&l).ts_product(&r);
        for q in prod.reachable_state_indices().collect::<Vec<_>>() {
            let edges = prod.edges_from(q).unwrap().collect::<Vec<_>>();
            assert_eq!(edges.len(), 2);
            for (e, sym) in edges.iter().zip(['a', 'b']) {
                assert_eq!(prod.edge(q, sym).unwrap().target(), e.target());
            }
        }
    }

    #[test]
    fn product_with_a_nondeterministic_right_side() {
        use crate::ts::PredecessorIterable;
        use crate::{NTS, TransitionSystem};
        let l: MealyMachine = DTS::builder()
            .default_color(Void)
            .with_transitions([(0, 'a', 0, 1), (1, 'a', 1, 0)])
            .into_mealy(0);
        // two edges on 'a' leave state 0
        let r = NTS::builder()
            .default_color(Void)
            .with_transitions([(0, 'a', 0), (0, 'a', 1), (1, 'a', 0)])
            .into_nts();
        let prod = (&l).ts_product(&r);
        let mut targets: Vec<_> = prod
            .edges_from(ProductIndex(0, 0))
            .unwrap()
            .map(|e| e.target())
            .collect();
        targets.sort();
        assert_eq!(targets, vec![ProductIndex(1, 0), ProductIndex(1, 1)]);
        let mut sources: Vec<_> = prod
            .predecessors(ProductIndex(0, 0))
            .unwrap()
            .map(|e| e.source())
            .collect();
        sources.sort();
        assert_eq!(sources, vec![ProductIndex(1, 0), ProductIndex(1, 1)]);
    }
}
