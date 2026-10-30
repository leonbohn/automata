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
use crate::{
    alphabet::{Alphabet, Matcher},
    math,
};
use itertools::Itertools;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

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
    expressions: BTreeMap<SymbolOf<Ts>, EdgeExpression<Ts>>,
    partition: Partition<Ts::StateIndex>,
    class_of: math::FxIndexMap<Ts::StateIndex, usize>,
}

impl<Ts: Deterministic + Pointed> Pointed for Quotient<Ts> {
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

    /// Creates a new quotient of the given transition system by the give [`Partition`].
    pub fn new(ts: Ts, partition: Partition<Ts::StateIndex>) -> Self {
        let class_of = partition
            .iter()
            .enumerate()
            .flat_map(|(i, class)| class.iter().map(move |q| (*q, i)))
            .collect();
        Self {
            class_of,
            expressions: ts
                .alphabet()
                .universe()
                .map(|sym| (sym, ts.alphabet().make_expression(sym).clone()))
                .collect(),
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
        let it = self.class_iter_by_id(state)?;
        it.map(|o| self.ts.state_color(o).map(Cow::into_owned))
            .collect::<Option<Vec<_>>>()
            .map(Cow::Owned)
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
        let (states, colors): (BTreeSet<_>, Vec<_>) = self
            .class_iter_by_id(origin)?
            .filter_map(|q| {
                self.ts.edge(q, symbol).map(|tt| {
                    (
                        self.find_id_by_state(tt.target()).expect("Unknown state"),
                        tt.color().clone(),
                    )
                })
            })
            .unzip();

        match states.len() {
            0 => None,
            1 => {
                let expression = self
                    .expressions
                    .iter()
                    .find_map(|(_, expr)| {
                        if symbol.matches(expr) {
                            Some(expr)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                Some(EdgeRef::owned(
                    origin,
                    expression,
                    colors,
                    states.into_iter().next().unwrap(),
                ))
            }
            _ => {
                let string = format!(
                    "{{{}}}",
                    states.iter().map(|idx| idx.to_string()).join(", ")
                );
                panic!(
                    "From {origin}|{} on symbol {:?}, we reach {} while precisely one state should be reached!",
                    self.class_iter_by_id(origin)
                        .unwrap()
                        .map(|c| format!("{c:?}"))
                        .join(", "),
                    symbol,
                    string
                )
            }
        }
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
