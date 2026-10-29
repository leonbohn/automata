//! Traversals of transition systems.
//!
//! - [`Bfs`] and [`Dfs`] yield the states that are reachable from a set of start states, [`BfsEdges`]
//!   yields the traversed edges instead.
//! - [`AccessWords`] performs a single breadth-first search and remembers, for every state it
//!   discovers, the predecessor and the symbol used to get there. From this tree the
//!   length-lexicographically minimal word reaching a state can be reconstructed on demand, so that
//!   memory is linear in the number of states instead of linear in the total length of all words.
//!
//! All traversals are lazy and never panic if a start state does not exist; they simply do not
//! yield it.

use crate::TransitionSystem;
use crate::alphabet::Expression;
use crate::congruence::MinimalRepresentative;
use crate::ts::{IsEdge, StateIndex, StateMap, StateSet, SymbolOf};
use std::collections::VecDeque;

/// Breadth-first traversal that yields the states reachable from a set of start states.
///
/// States are yielded in the order in which they are dequeued, i.e. by increasing distance from
/// the start states. A start state that does not exist in the transition system is skipped.
///
/// ```
/// use automata::TransitionSystem;
/// use automata::ts::visit::Bfs;
/// use automata::automaton::DFA;
///
/// let dfa = DFA::builder()
///     .with_state_colors([false, false, true])
///     .with_edges([(0, 'a', 1), (1, 'a', 2), (2, 'a', 2)])
///     .into_dfa(0);
/// assert_eq!(Bfs::new(&dfa, 1).collect::<Vec<_>>(), vec![1, 2]);
/// ```
pub struct Bfs<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    seen: StateSet<Ts::StateIndex>,
    queue: VecDeque<StateIndex<Ts>>,
}

impl<'a, Ts: TransitionSystem> Bfs<'a, Ts> {
    /// Creates a traversal of the states reachable from `origin`.
    pub fn new(ts: &'a Ts, origin: StateIndex<Ts>) -> Self {
        Self::from_starts(ts, [origin])
    }

    /// Creates a traversal of the states reachable from any of the `starts`.
    pub fn from_starts(ts: &'a Ts, starts: impl IntoIterator<Item = StateIndex<Ts>>) -> Self {
        let mut seen = StateSet::new(ts.state_bound());
        let mut queue = VecDeque::new();
        for start in starts {
            if seen.insert(start) {
                queue.push_back(start);
            }
        }
        Self { ts, seen, queue }
    }
}

impl<Ts: TransitionSystem> Iterator for Bfs<'_, Ts> {
    type Item = StateIndex<Ts>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let q = self.queue.pop_front()?;
            let Some(edges) = self.ts.edges_from(q) else {
                continue;
            };
            for edge in edges {
                if self.seen.insert(edge.target()) {
                    self.queue.push_back(edge.target());
                }
            }
            return Some(q);
        }
    }
}

/// Breadth-first traversal that yields the edges that are reachable from a set of start states.
/// Every reachable edge is yielded exactly once.
pub struct BfsEdges<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    seen: StateSet<Ts::StateIndex>,
    it: Option<Ts::EdgesFromIter<'a>>,
    queue: VecDeque<StateIndex<Ts>>,
}

impl<'a, Ts: TransitionSystem> BfsEdges<'a, Ts> {
    /// Creates a traversal of the edges reachable from `origin`.
    pub fn new(ts: &'a Ts, origin: StateIndex<Ts>) -> Self {
        let mut seen = StateSet::new(ts.state_bound());
        seen.insert(origin);
        Self {
            ts,
            seen,
            it: None,
            queue: VecDeque::from([origin]),
        }
    }
}

impl<'a, Ts: TransitionSystem> Iterator for BfsEdges<'a, Ts> {
    type Item = Ts::EdgeRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(edge) = self.it.as_mut().and_then(Iterator::next) {
                if self.seen.insert(edge.target()) {
                    self.queue.push_back(edge.target());
                }
                return Some(edge);
            }
            let q = self.queue.pop_front()?;
            self.it = self.ts.edges_from(q);
        }
    }
}

/// Depth-first traversal that yields the states reachable from a set of start states in preorder,
/// i.e. a state is yielded when it is first discovered. A start state that does not exist in the
/// transition system is skipped.
pub struct Dfs<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    seen: StateSet<Ts::StateIndex>,
    stack: Vec<Ts::EdgesFromIter<'a>>,
    starts: VecDeque<StateIndex<Ts>>,
}

impl<'a, Ts: TransitionSystem> Dfs<'a, Ts> {
    /// Creates a traversal of the states reachable from `origin`.
    pub fn new(ts: &'a Ts, origin: StateIndex<Ts>) -> Self {
        Self::from_starts(ts, [origin])
    }

    /// Creates a traversal of the states reachable from any of the `starts`. The start states are
    /// explored one after the other, in the given order.
    pub fn from_starts(ts: &'a Ts, starts: impl IntoIterator<Item = StateIndex<Ts>>) -> Self {
        Self {
            ts,
            seen: StateSet::new(ts.state_bound()),
            stack: Vec::new(),
            starts: starts.into_iter().collect(),
        }
    }
}

impl<Ts: TransitionSystem> Iterator for Dfs<'_, Ts> {
    type Item = StateIndex<Ts>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            while let Some(top) = self.stack.last_mut() {
                let Some(edge) = top.next() else {
                    self.stack.pop();
                    continue;
                };
                let target = edge.target();
                if self.seen.insert(target) {
                    if let Some(edges) = self.ts.edges_from(target) {
                        self.stack.push(edges);
                    }
                    return Some(target);
                }
            }
            let start = self.starts.pop_front()?;
            if self.seen.insert(start)
                && let Some(edges) = self.ts.edges_from(start)
            {
                self.stack.push(edges);
                return Some(start);
            }
        }
    }
}

#[derive(Clone, Debug)]
struct AccessNode<Idx, Sym> {
    parent: Option<(Idx, Sym)>,
    rank: usize,
}

/// A breadth-first search tree from a single origin state, from which the length-lexicographically
/// minimal access word of every reachable state can be reconstructed.
///
/// The search is a FIFO breadth-first search. Whenever a state is dequeued, the pairs
/// `(symbol, target)` of all its outgoing edges are collected (an expression may match several
/// symbols) and sorted by symbol before the targets are enqueued. Consequently the first discovery
/// of a state happens along its length-lexicographically minimal word, and states are discovered
/// and dequeued in the length-lexicographic order of their minimal words.
///
/// `AccessWords` is an iterator over the states in exactly that order and is lazy: the search only
/// advances as far as needed. [`AccessWords::word`] works for every state that was discovered so
/// far, [`AccessWords::word_to`] advances the search until the requested state is discovered.
///
/// ```
/// use automata::TransitionSystem;
/// use automata::ts::visit::AccessWords;
/// use automata::automaton::DFA;
///
/// let dfa = DFA::builder()
///     .with_state_colors([false, false, true])
///     .with_edges([(0, 'b', 1), (0, 'a', 0), (1, 'a', 2), (1, 'b', 0), (2, 'a', 2), (2, 'b', 2)])
///     .into_dfa(0);
/// let mut words = AccessWords::new(&dfa, 0);
/// assert_eq!(words.word_to(2), Some(vec!['b', 'a']));
/// ```
pub struct AccessWords<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    nodes: StateMap<Ts::StateIndex, AccessNode<Ts::StateIndex, SymbolOf<Ts>>>,
    order: Vec<StateIndex<Ts>>,
    head: usize,
}

impl<'a, Ts: TransitionSystem> AccessWords<'a, Ts> {
    /// Starts a search from `origin`. If `origin` does not exist in `ts`, nothing is reachable.
    pub fn new(ts: &'a Ts, origin: StateIndex<Ts>) -> Self {
        let mut nodes = StateMap::new(ts.state_bound());
        let mut order = Vec::new();
        if ts.edges_from(origin).is_some() {
            nodes.insert(
                origin,
                AccessNode {
                    parent: None,
                    rank: 0,
                },
            );
            order.push(origin);
        }
        Self {
            ts,
            nodes,
            order,
            head: 0,
        }
    }

    /// Runs the search to completion, so that every reachable state is discovered.
    pub fn complete(&mut self) -> &mut Self {
        self.by_ref().for_each(drop);
        self
    }

    /// Returns `true` if `state` was discovered by the search so far.
    pub fn is_discovered(&self, state: StateIndex<Ts>) -> bool {
        self.nodes.contains_key(&state)
    }

    /// Returns the position of `state` in the length-lexicographic order of access words, if it was
    /// discovered so far.
    pub fn rank(&self, state: StateIndex<Ts>) -> Option<usize> {
        self.nodes.get(&state).map(|n| n.rank)
    }

    /// Reconstructs the length-lexicographically minimal word that leads from the origin to
    /// `state`, provided `state` was discovered so far.
    pub fn word(&self, state: StateIndex<Ts>) -> Option<Vec<SymbolOf<Ts>>> {
        let mut word = Vec::new();
        let mut current = state;
        while let Some((parent, sym)) = self.nodes.get(&current)?.parent {
            word.push(sym);
            current = parent;
        }
        word.reverse();
        Some(word)
    }

    /// Advances the search until `state` is discovered and returns its access word, or `None` if
    /// `state` is not reachable.
    pub fn word_to(&mut self, state: StateIndex<Ts>) -> Option<Vec<SymbolOf<Ts>>> {
        while !self.is_discovered(state) {
            self.next()?;
        }
        self.word(state)
    }

    /// Turns the search into an iterator over [`MinimalRepresentative`]s.
    pub fn into_representatives(self) -> LengthLexicographicMinimalRepresentatives<'a, Ts> {
        LengthLexicographicMinimalRepresentatives(self)
    }

    fn expand(&mut self, state: StateIndex<Ts>) {
        let Some(edges) = self.ts.edges_from(state) else {
            return;
        };
        let mut successors: Vec<(SymbolOf<Ts>, StateIndex<Ts>)> = edges
            .flat_map(|edge| {
                let target = edge.target();
                edge.expression().symbols().map(move |sym| (sym, target))
            })
            .collect();
        successors.sort_unstable();
        for (sym, target) in successors {
            if !self.nodes.contains_key(&target) {
                self.nodes.insert(
                    target,
                    AccessNode {
                        parent: Some((state, sym)),
                        rank: self.order.len(),
                    },
                );
                self.order.push(target);
            }
        }
    }
}

impl<Ts: TransitionSystem> Iterator for AccessWords<'_, Ts> {
    type Item = StateIndex<Ts>;

    fn next(&mut self) -> Option<Self::Item> {
        let state = *self.order.get(self.head)?;
        self.head += 1;
        self.expand(state);
        Some(state)
    }
}

/// Iterator over the length-lexicographically minimal representatives of the states reachable from
/// an origin, in increasing order. It is a thin layer on top of [`AccessWords`] that reconstructs
/// the word of every state it yields.
pub struct LengthLexicographicMinimalRepresentatives<'a, Ts: TransitionSystem>(AccessWords<'a, Ts>);

impl<'a, Ts: TransitionSystem> LengthLexicographicMinimalRepresentatives<'a, Ts> {
    /// Creates an iterator over the length-lexicographically minimal representatives of the
    /// states that are reachable from `origin`, in increasing order.
    pub fn new(ts: &'a Ts, origin: StateIndex<Ts>) -> Self {
        Self(AccessWords::new(ts, origin))
    }
}

impl<Ts: TransitionSystem> Iterator for LengthLexicographicMinimalRepresentatives<'_, Ts> {
    type Item = MinimalRepresentative<Ts>;

    fn next(&mut self) -> Option<Self::Item> {
        let state = self.0.next()?;
        let word = self.0.word(state).expect("yielded states are discovered");
        Some(MinimalRepresentative::new(word, state))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TransitionSystem;
    use crate::alphabet::Expression;
    use crate::automaton::DFA;
    use crate::congruence::MinimalRepresentative;
    use crate::ts::States;
    use crate::ts::{Builder, Deterministic, IsEdge};
    use itertools::Itertools;
    use std::collections::{BTreeMap, BTreeSet};

    /// Independent reference: relaxes `best[q]` with `best[p] + sym` for all edges until nothing
    /// changes, comparing words length-lexicographically.
    fn reference<Ts: TransitionSystem>(
        ts: &Ts,
        origin: StateIndex<Ts>,
    ) -> BTreeMap<StateIndex<Ts>, Vec<SymbolOf<Ts>>> {
        let mut best: BTreeMap<StateIndex<Ts>, Vec<SymbolOf<Ts>>> = BTreeMap::new();
        best.insert(origin, vec![]);
        loop {
            let mut changed = false;
            for (q, word) in best.clone() {
                for edge in ts.edges_from(q).unwrap() {
                    for sym in edge.expression().symbols() {
                        let mut candidate = word.clone();
                        candidate.push(sym);
                        let better = best
                            .get(&edge.target())
                            .is_none_or(|old| (candidate.len(), &candidate) < (old.len(), old));
                        if better {
                            best.insert(edge.target(), candidate);
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                return best;
            }
        }
    }

    fn check_against_reference<Ts: TransitionSystem>(ts: &Ts, origin: StateIndex<Ts>) {
        let expected = reference(ts, origin);
        let expected_order = expected
            .iter()
            .sorted_by_key(|(_, w)| (w.len(), (*w).clone()))
            .map(|(q, w)| (*q, w.clone()))
            .collect_vec();

        let actual = LengthLexicographicMinimalRepresentatives::new(ts, origin)
            .map(MinimalRepresentative::into_name)
            .collect_vec();
        assert_eq!(actual, expected_order);

        let mut words = AccessWords::new(ts, origin);
        words.complete();
        for (q, w) in &expected {
            assert_eq!(words.word(*q).as_ref(), Some(w));
        }

        let reachable: BTreeSet<_> = expected.keys().copied().collect();
        assert_eq!(Bfs::new(ts, origin).collect::<BTreeSet<_>>(), reachable);
        assert_eq!(Bfs::new(ts, origin).count(), reachable.len());
        assert_eq!(Dfs::new(ts, origin).collect::<BTreeSet<_>>(), reachable);
        assert_eq!(Dfs::new(ts, origin).count(), reachable.len());
    }

    #[test]
    fn small_example() {
        let dfa = DFA::builder()
            .with_state_colors([false, false, true])
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 0),
                (1, 'a', 2),
                (1, 'b', 0),
                (2, 'a', 2),
                (2, 'b', 2),
            ])
            .into_dfa(0);

        assert_eq!(
            dfa.minimal_representatives_iter_from(0).collect_vec(),
            vec![
                MinimalRepresentative::new(vec![], 0u32),
                MinimalRepresentative::new(vec!['a'], 1),
                MinimalRepresentative::new(vec!['a', 'a'], 2)
            ]
        );
        assert_eq!(dfa.reachable_state_indices().collect_vec(), vec![0, 1, 2]);
        assert_eq!(dfa.reachable_state_indices_from(2).collect_vec(), vec![2]);
        assert_eq!(dfa.reachable_edges_from(1).count(), 6);
    }

    #[test]
    fn dfs_is_preorder() {
        let dfa = DFA::builder()
            .with_state_colors([false; 4])
            .with_edges([(0, 'a', 1), (0, 'b', 2), (1, 'a', 3), (2, 'a', 3)])
            .into_dfa(0);
        assert_eq!(Dfs::new(&dfa, 0).collect_vec(), vec![0, 1, 3, 2]);
        assert_eq!(Bfs::new(&dfa, 0).collect_vec(), vec![0, 1, 2, 3]);
        assert_eq!(Dfs::from_starts(&dfa, [2, 1]).collect_vec(), vec![2, 3, 1]);
    }

    #[test]
    fn missing_origin_yields_nothing() {
        let dfa = DFA::builder()
            .with_state_colors([false, true])
            .with_edges([(0, 'a', 1), (1, 'a', 1)])
            .into_dfa(0);
        assert_eq!(Bfs::new(&dfa, 7).count(), 0);
        assert_eq!(Dfs::new(&dfa, 7).count(), 0);
        assert_eq!(BfsEdges::new(&dfa, 7).count(), 0);
        assert_eq!(dfa.minimal_representatives_iter_from(7).count(), 0);
        assert_eq!(dfa.word_from_to(7, 0), None);
        assert_eq!(dfa.word_from_to(0, 7), None);
        assert_eq!(dfa.minimal_representative(7), None);
    }

    #[test]
    fn access_words_are_lazy_and_minimal() {
        let dfa = DFA::builder()
            .with_state_colors([false; 4])
            .with_edges([(0, 'b', 1), (0, 'a', 2), (2, 'b', 3), (1, 'a', 3)])
            .into_dfa(0);
        let mut words = AccessWords::new(&dfa, 0);
        assert_eq!(words.word_to(1), Some(vec!['b']));
        // 'a' sorts before 'b', so 3 is first discovered from 2 via "ab", not from 1 via "ba"
        assert_eq!(words.word_to(3), Some(vec!['a', 'b']));
        assert_eq!(dfa.word_from_to(1, 3), Some(vec!['a']));
        assert_eq!(dfa.word_from_to(3, 0), None);
    }

    #[test]
    fn matches_reference_on_pseudo_random_systems() {
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut next = move |bound: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % bound
        };
        for _ in 0..200 {
            let size = 1 + next(12) as u32;
            let mut edges = vec![];
            for q in 0..size {
                for sym in ['a', 'b', 'c'] {
                    if next(4) != 0 {
                        edges.push((q, sym, next(size as u64) as u32));
                    }
                }
            }
            let dts = Builder::without_colors()
                .with_transitions(edges)
                .into_dts_with_initial(0);
            // states without edges may be missing from the builder; only test existing origins
            if dts.contains_state_index(0) {
                check_against_reference(&dts, 0);
            }
        }
    }

    /// Regression test for #80: an edge matching several symbols must not yield its target
    /// several times.
    #[test]
    fn multi_symbol_edge_yields_each_state_once() {
        use crate::Void;
        use crate::alphabet::{Alphabet, PropAlphabet, PropExpression};
        use crate::ts::{ForAlphabet, Sproutable};

        let alphabet = PropAlphabet::<u32>::new(vec!["p".into(), "q".into()]);
        let mut ts = crate::DTS::for_alphabet(alphabet);
        let q0 = ts.add_state(Void);
        let q1 = ts.add_state(Void);
        ts.add_edge((q0, PropExpression::<u32>::universal(2), Void, q1));
        let reps = ts.minimal_representatives_iter_from(q0).collect_vec();
        assert_eq!(reps.len(), 2);
        assert_eq!(reps[1].state_index(), q1);
        assert_eq!(reps[1].len(), 1);
        let first_symbol = ts.alphabet().universe().min().unwrap();
        assert_eq!(reps[1].clone().into_inner(), vec![first_symbol]);
    }

    /// Regression test for #81: among parallel edges the smallest symbol wins, regardless of the
    /// order in which the edges are listed.
    #[test]
    fn parallel_edges_use_smallest_symbol() {
        for edges in [[(0, 'a', 1), (0, 'b', 1)], [(0, 'b', 1), (0, 'a', 1)]] {
            let dts = Builder::without_colors()
                .with_transitions(edges)
                .into_dts_with_initial(0);
            assert_eq!(dts.word_from_to(0, 1), Some(vec!['a']));
            assert_eq!(
                dts.minimal_representative(1).unwrap().into_inner(),
                vec!['a']
            );
        }
    }

    #[test]
    fn propositional_alphabet() {
        use crate::Void;
        use crate::alphabet::{PropAlphabet, PropExpression};
        use crate::ts::ForAlphabet;
        use crate::ts::Sproutable;

        let alphabet = PropAlphabet::<u32>::new(vec!["p".into(), "q".into(), "r".into()]);
        let mut ts = crate::DTS::for_alphabet(alphabet);
        let states = (0..4).map(|_| ts.add_state(Void)).collect_vec();
        // an expression that matches several symbols and leads to a state that is also
        // reachable through a single, but lexicographically larger symbol later on
        ts.add_edge((
            states[0],
            PropExpression::<u32>::new(3, "x_0 & !x_1"),
            Void,
            states[1],
        ));
        ts.add_edge((
            states[0],
            PropExpression::<u32>::new(3, "x_1"),
            Void,
            states[2],
        ));
        ts.add_edge((
            states[1],
            PropExpression::<u32>::new(3, "x_0 | x_2"),
            Void,
            states[3],
        ));
        ts.add_edge((
            states[2],
            PropExpression::<u32>::new(3, "!x_0 & !x_1 & !x_2"),
            Void,
            states[3],
        ));
        ts.add_edge((
            states[3],
            PropExpression::<u32>::universal(3),
            Void,
            states[0],
        ));
        check_against_reference(&ts, states[0]);
        check_against_reference(&ts, states[2]);
        assert_eq!(Bfs::new(&ts, states[1]).count(), 4);
    }
}
