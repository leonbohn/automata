use crate::DTS;
use crate::Void;
use crate::ts::States;
use crate::ts::{EdgeOf, EdgeRef};
use crate::{
    RightCongruence,
    partition::Partition,
    representation::CollectPointed,
    ts::{Deterministic, EdgeExpression, Pointed, StateIndex, SymbolOf, TransitionSystem},
};
use crate::{alphabet::Alphabet, math};
use std::borrow::Cow;

/// A quotient takes a transition system and merges states which are in the same
/// congruence class of some [`Partition`]. We assume that the [`Partition`] is
/// a congruence, meaning if we have two classes `X, Y`, then for all `p`, `q` in X
/// and all symbols `a` in the alphabet, there is an edge from `p` on `a` to some
/// state in `Y` if and only if the same is true for `q`. Thus, there is an edge
/// between states (which are congruence classes) of the [`Quotient`] for some symbol
/// `a`, if there is an edge between the states contained in the class.
///
/// In the implementation of [`TransitionSystem`] for [`Quotient`], the edge and
/// state colors are [`Vec`]s of the respective colors of the underlying transition
/// system, where we simply collect all colors.
#[derive(Debug, Clone)]
pub struct Quotient<Ts: TransitionSystem> {
    ts: Ts,
    /// The symbols of the alphabet in ascending order with their expressions.
    expressions: Vec<(SymbolOf<Ts>, EdgeExpression<Ts>)>,
    partition: Partition<Ts::StateIndex>,
    class_of: math::FxIndexMap<Ts::StateIndex, usize>,
    /// The edge of each class on each symbol, class-major: the entry of class `c` and the symbol
    /// at position `i` of `expressions` is `table[c * expressions.len() + i]`. Computed once in
    /// the constructor.
    table: Vec<Option<ClassEdge<Ts>>>,
    /// The state colors of the states in each class.
    state_colors: Vec<Vec<Ts::StateColor>>,
}

/// The target class and the edge colors of the states of a class for one symbol.
#[derive(Debug, Clone)]
struct ClassEdge<Ts: TransitionSystem> {
    target: usize,
    colors: Vec<Ts::EdgeColor>,
}

impl<Ts: Deterministic + Pointed> Pointed for Quotient<Ts> {
    /// # Panics
    /// Panics if the partition does not contain the initial state of the underlying system.
    fn initial(&self) -> usize {
        self.find_id_by_state(self.ts.initial())
            .expect("Initial class must exist")
    }
}

impl<Ts: TransitionSystem> Quotient<Ts> {
    /// Returns a reference to the [`Partition`] underlying the quotient.
    pub fn partition(&self) -> &Partition<Ts::StateIndex> {
        &self.partition
    }

    /// Gives a reference to the underlying transition system.
    pub fn ts(&self) -> &Ts {
        &self.ts
    }

    /// Indexes into the underlying partition and tries to get a representative for the indexed class.
    ///
    /// # Panics
    /// Panics if the class does not exist or is empty.
    pub fn unwrap_class_representative(&self, id: usize) -> Ts::StateIndex {
        *self
            .partition
            .get(id)
            .expect("Class must exist")
            .iter()
            .next()
            .expect("Class must not be empty")
    }

    /// Returns an iterator over the indices in the quotient class with the given `id`.
    /// If no such class exists, `None` is returned.
    pub fn class_iter_by_id(&self, id: usize) -> Option<impl Iterator<Item = Ts::StateIndex> + '_> {
        self.partition.get(id).map(|s| s.iter().cloned())
    }

    /// Tries to find the id of the quotient class containing the given state `q`. If
    /// the state is not in the partition, `None` is returned.
    pub fn find_id_by_state(&self, q: Ts::StateIndex) -> Option<usize> {
        self.class_of.get(&q).copied()
    }

    /// Extracts the underlying right congruence by erasing the state and edge colors and then collecting
    /// into a [`RightCongruence`].
    pub fn underlying_right_congruence(&self) -> RightCongruence<DTS<Ts::Alphabet, Void, Void>>
    where
        Ts: Deterministic + Pointed,
    {
        self.erase_state_colors()
            .erase_edge_colors()
            .collect_right_congruence()
    }
}

impl<Ts: Deterministic> Quotient<Ts> {
    /// Creates a new quotient of the given transition system by the give [`Partition`]. The edges
    /// and state colors of all classes are computed here, so that looking them up later does
    /// not allocate. A class that has different targets on a symbol is not a congruence, in that
    /// case the target of the first state of the class is used.
    pub fn new(ts: Ts, partition: Partition<Ts::StateIndex>) -> Self {
        let class_of: math::FxIndexMap<_, _> = partition
            .iter()
            .enumerate()
            .flat_map(|(i, class)| class.iter().map(move |q| (*q, i)))
            .collect();
        let mut expressions: Vec<_> = ts
            .alphabet()
            .universe()
            .map(|sym| (sym, ts.alphabet().make_expression(sym)))
            .collect();
        expressions.sort_by_key(|(sym, _)| *sym);

        let mut table = Vec::with_capacity(partition.len() * expressions.len());
        let mut state_colors = Vec::with_capacity(partition.len());
        for class in partition.iter() {
            state_colors.push(
                class
                    .iter()
                    .filter_map(|q| ts.state_color(*q).map(Cow::into_owned))
                    .collect(),
            );
            for (sym, _) in &expressions {
                let mut target = None;
                let mut colors = Vec::new();
                for e in class.iter().filter_map(|q| ts.edge(*q, *sym)) {
                    let Some(&t) = class_of.get(&e.target()) else {
                        continue;
                    };
                    debug_assert!(
                        target.is_none_or(|u| u == t),
                        "partition is not a congruence"
                    );
                    target.get_or_insert(t);
                    colors.push(e.color().clone());
                }
                table.push(target.map(|target| ClassEdge { target, colors }));
            }
        }
        Self {
            class_of,
            expressions,
            table,
            state_colors,
            ts,
            partition,
        }
    }
}

/// Allows iterating over the edges originating from a state in the [`Quotient`]
/// of a [`TransitionSystem`].
#[derive(Clone)]
pub struct QuotientEdgesFrom<'a, Ts: TransitionSystem, I> {
    it: I,
    quot: &'a Quotient<Ts>,
    class: usize,
}

impl<'a, Ts, I> Iterator for QuotientEdgesFrom<'a, Ts, I>
where
    Ts: Deterministic,
    I: Iterator<Item = SymbolOf<Ts>>,
{
    type Item = EdgeRef<'a, usize, EdgeExpression<Ts>, Vec<Ts::EdgeColor>>;

    fn next(&mut self) -> Option<Self::Item> {
        let sym = self.it.next()?;
        self.quot.edge(self.class, sym)
    }
}

impl<'a, Ts: TransitionSystem, I> QuotientEdgesFrom<'a, Ts, I> {
    /// Creates a new iterator over the edges originating from a state in a
    /// [`Quotient`] of a [`TransitionSystem`].
    pub fn new(ts: &'a Quotient<Ts>, it: I, class: usize) -> Self {
        Self {
            it,
            quot: ts,
            class,
        }
    }
}

impl<Ts: Deterministic> TransitionSystem for Quotient<Ts> {
    type StateIndex = usize;

    type StateColor = Vec<Ts::StateColor>;

    type EdgeColor = Vec<Ts::EdgeColor>;

    type EdgesFromIter<'this>
        = QuotientEdgesFrom<'this, Ts, <Self::Alphabet as Alphabet>::Universe<'this>>
    where
        Self: 'this;

    type Alphabet = Ts::Alphabet;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.state_colors.get(state).map(Cow::Borrowed)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        if self.partition.len() <= state {
            None
        } else {
            Some(QuotientEdgesFrom::new(
                self,
                self.alphabet().universe(),
                state,
            ))
        }
    }
}

impl<Ts: Deterministic> States for Quotient<Ts> {
    type StatesIter<'this>
        = std::ops::Range<usize>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        0..self.partition.len()
    }

    fn state_count(&self) -> usize {
        self.partition.len()
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        index < self.partition.len()
    }
}
impl<D: Deterministic> Deterministic for Quotient<D> {
    fn edge(&self, origin: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        let i = self
            .expressions
            .binary_search_by_key(&symbol, |(sym, _)| *sym)
            .ok()?;
        let edge = self
            .table
            .get(origin * self.expressions.len() + i)?
            .as_ref()?;
        Some(EdgeRef::borrowed(
            origin,
            &self.expressions[i].1,
            &edge.colors,
            edge.target,
        ))
    }
}

#[cfg(test)]
mod tests {
    use crate::States;
    use crate::partition::Partition;
    use crate::tests::wiki_dfa;
    use crate::ts::Deterministic;

    #[test]
    fn quotient_test() {
        let dfa = wiki_dfa();
        let p = Partition::new([vec![0, 1], vec![5], vec![2, 3, 4]]);
        let a = dfa.quotient(p);

        for (i, p) in [0, 2, 1, 1, 2, 1].into_iter().enumerate() {
            let q = i / 2;
            let sym = ['a', 'b'][i % 2];
            assert_eq!(a.successor(q, sym), Some(p));
        }
    }

    #[test]
    fn quotient_collects_colors_of_the_class() {
        use crate::TransitionSystem;
        let dfa = wiki_dfa();
        let a = dfa
            .clone()
            .quotient(Partition::new([vec![0, 1], vec![5], vec![2, 3, 4]]));
        for (class, members) in [vec![0, 1], vec![5], vec![2, 3, 4]].into_iter().enumerate() {
            let expected: Vec<_> = members
                .iter()
                .map(|q| *dfa.state_color(*q).unwrap())
                .collect();
            assert_eq!(a.state_color(class).unwrap().into_owned(), expected);
            for sym in ['a', 'b'] {
                assert_eq!(a.edge(class, sym).unwrap().color().len(), members.len());
            }
        }
        assert!(a.edge(3, 'a').is_none());
        assert!(a.edge(0, 'z').is_none());
    }

    #[test]
    fn quotient_iterates_edges() {
        use crate::TransitionSystem;
        use crate::ts::Deterministic;
        let dfa = wiki_dfa();
        let a = dfa.quotient(Partition::new([vec![0, 1], vec![5], vec![2, 3, 4]]));
        for q in a.states() {
            let edges = a.edges_from(q).unwrap().collect::<Vec<_>>();
            assert_eq!(edges.len(), 2);
            for (e, sym) in edges.iter().zip(['a', 'b']) {
                assert_eq!(a.edge(q, sym).unwrap().target(), e.target());
            }
        }
    }
}
