//! Partition refinement algorithms for determinsitic finite automata. This module implements the
//! Hopcroft and Moore algorithms for minimizing deterministic finite automata. There are two main
//! variants of the algorithm, one for Moore machines and one for Mealy machines. They differ only
//! on the way they handle the output of the automaton. Specifically, for Moore machines, we consider
//! the output of the state, whereas for Mealy machines, we consider the output of the transition.
//! It is necessary to have two distinct algorithms (so with different names) as there might be
//! transition systems which have outputs on both the states and the transitions.
use crate::DTS;
use crate::Void;
use crate::ts::States;
use std::{collections::BTreeSet, time::Instant};

use crate::automaton::{MealyMachine, MooreMachine};
use crate::representation::CollectPointed;
use crate::ts::{Deterministic, EdgeColor, StateColor};
use crate::{Color, math, partition::Partition};
use crate::{Congruence, TransitionSystem};
use itertools::Itertools;
use tracing::{debug, trace};

/// Predecessor lists for one symbol in compressed form, each entry is a `(source, label)` pair.
struct Predecessors {
    offsets: Vec<usize>,
    entries: Vec<(usize, usize)>,
}

impl Predecessors {
    /// Builds the lists from `(target, source, label)` triples.
    fn new(n: usize, edges: Vec<(usize, usize, usize)>) -> Self {
        let mut offsets = vec![0; n + 1];
        for (target, _, _) in &edges {
            offsets[target + 1] += 1;
        }
        for i in 0..n {
            offsets[i + 1] += offsets[i];
        }
        let mut fill = offsets.clone();
        let mut entries = vec![(0, 0); edges.len()];
        for (target, source, label) in edges {
            entries[fill[target]] = (source, label);
            fill[target] += 1;
        }
        Self { offsets, entries }
    }

    fn of(&self, target: usize) -> &[(usize, usize)] {
        &self.entries[self.offsets[target]..self.offsets[target + 1]]
    }
}

/// Hopcroft's algorithm on dense indices. `initial` assigns every state a block id in `0..m` (all of
/// which must be used), `pre` contains the predecessors per symbol and `labels` is the number of
/// distinct edge labels. Returns the block id of every state in the coarsest stable refinement.
fn refine(n: usize, labels: usize, pre: Vec<Predecessors>, initial: Vec<usize>) -> Vec<usize> {
    let k = pre.len();
    let mut block_of = initial;
    let blocks = block_of.iter().max().map_or(0, |m| m + 1);

    let mut elems: Vec<usize> = (0..n).collect();
    elems.sort_by_key(|&q| block_of[q]);
    let mut pos = vec![0; n];
    for (i, &q) in elems.iter().enumerate() {
        pos[q] = i;
    }
    let mut first = vec![0; blocks];
    let mut size = vec![0; blocks];
    for &q in &elems {
        size[block_of[q]] += 1;
    }
    for b in 1..blocks {
        first[b] = first[b - 1] + size[b - 1];
    }
    let mut marked = vec![0; blocks];

    let mut in_work = vec![true; blocks * k];
    let mut work: Vec<(usize, usize)> = (0..blocks)
        .flat_map(|b| (0..k).map(move |s| (b, s)))
        .collect();

    let mut touched = Vec::new();
    let mut found: Vec<(usize, usize)> = Vec::new();
    while let Some((splitter, s)) = work.pop() {
        in_work[splitter * k + s] = false;

        found.clear();
        for &t in &elems[first[splitter]..first[splitter] + size[splitter]] {
            found.extend(pre[s].of(t).iter().map(|&(q, label)| (label, q)));
        }
        if labels > 1 {
            found.sort_unstable();
        }

        for group in found.chunk_by(|a, b| a.0 == b.0) {
            touched.clear();
            for &(_, q) in group {
                let b = block_of[q];
                if marked[b] == 0 {
                    touched.push(b);
                }
                let target = first[b] + marked[b];
                let p = pos[q];
                let other = elems[target];
                elems.swap(p, target);
                pos[q] = target;
                pos[other] = p;
                marked[b] += 1;
            }

            for &b in &touched {
                let m = std::mem::take(&mut marked[b]);
                if m == size[b] {
                    continue;
                }
                let nb = first.len();
                first.push(first[b]);
                size.push(m);
                marked.push(0);
                first[b] += m;
                size[b] -= m;
                for &q in &elems[first[nb]..first[nb] + m] {
                    block_of[q] = nb;
                }
                in_work.extend(std::iter::repeat_n(false, k));
                for s2 in 0..k {
                    let add = if in_work[b * k + s2] || size[nb] <= size[b] {
                        nb
                    } else {
                        b
                    };
                    in_work[add * k + s2] = true;
                    work.push((add, s2));
                }
            }
        }
    }
    block_of
}

fn collect_partition<I: crate::ts::IdType>(states: &[I], block_of: &[usize]) -> Partition<I> {
    let mut blocks: math::FxIndexMap<usize, BTreeSet<I>> = math::FxIndexMap::default();
    for (q, b) in states.iter().zip(block_of) {
        blocks.entry(*b).or_default().insert(*q);
    }
    let mut blocks: Vec<_> = blocks.into_values().collect();
    blocks.sort();
    blocks.into()
}

/// Computes the maximal bisimulation of the given something that behaves like a mealy machine. The returned
/// partition is a [`Partition`] of the state indices, where any states in the same class of the
/// returned partition are pairwise bisimilar. This means for any *non-empty* input, they produce
/// the same sequence of outputs.
pub fn mealy_greatest_bisimulation<D>(mm: D) -> Partition<D::StateIndex>
where
    D: Deterministic + States,
    EdgeColor<D>: Color + Eq + std::hash::Hash,
{
    let start = Instant::now();
    let mut ids = crate::ts::CompactIdMap::new(mm.state_bound(), 0);
    for q in mm.states() {
        ids.get_or_insert(q);
    }
    let states = ids.states().to_vec();
    let symbols: Vec<_> = mm.symbols().collect();

    let mut labels: math::FxIndexMap<EdgeColor<D>, usize> = math::FxIndexMap::default();
    let mut raw = vec![Vec::new(); symbols.len()];
    for (s, sym) in symbols.iter().enumerate() {
        for (q, state) in states.iter().enumerate() {
            if let Some(t) = mm.edge(*state, *sym)
                && let Some(target) = ids.id(&t.target())
            {
                let next = labels.len();
                let label = *labels.entry(t.color().clone()).or_insert(next);
                raw[s].push((target, q, label));
            }
        }
    }
    let pre = raw
        .into_iter()
        .map(|e| Predecessors::new(states.len(), e))
        .collect();

    let block_of = refine(states.len(), labels.len(), pre, vec![0; states.len()]);
    debug!(
        "computing greatest bisimulation for Mealy Machine took {} microseconds",
        start.elapsed().as_micros()
    );
    collect_partition(&states, &block_of)
}

/// The [`MealyMachine`] that results from minimizing `D`. The state colors are the classes of
/// state colors that have been merged.
pub(crate) type MinimizedMealy<D> = MealyMachine<
    DTS<<D as TransitionSystem>::Alphabet, Vec<StateColor<D>>, <D as TransitionSystem>::EdgeColor>,
>;

/// Partition refinement algorithm for deterministic finite automata that have outputs on the edges.
/// Runs in O(n log n) time, where n is the number of states of the automaton and returns the unique
/// minimal automaton that is bisimilar to the input.
pub fn mealy_partition_refinement<D>(mm: D) -> MinimizedMealy<D>
where
    D: Congruence + States,
    EdgeColor<D>: Color + Eq + std::hash::Hash,
{
    let partition = mealy_greatest_bisimulation(&mm);
    trace!(
        "Building quotient with partition {{{}}}",
        partition
            .iter()
            .map(|set| format!("{{{}}}", set.iter().map(|c| format!("{c:?}")).join(", ")))
            .join(", ")
    );

    let start = Instant::now();

    let out = mm
        .quotient(partition)
        .map_edge_colors(|c| {
            // assert!(c.iter().all_equal());
            c[0].clone()
        })
        .collect_mealy();
    debug!(
        "Collecting into Mealy machine took {} microseconds",
        start.elapsed().as_micros()
    );
    out
}

/// Computes the maximal bisimulation for a given Moore machine. This is mainly used for
/// executing the partition refinement algorithm for Moore machines, see [`moore_partition_refinement`].
///
/// Two states of a mealy machine are considered to be bisimilar if and only if they have the same
/// output on all words. This gives a [`Partition`] of the state indices, where any states in the
/// same class of the returned partition are pairwise bisimilar.
pub fn moore_greatest_bisimulation<D>(mm: D) -> Partition<D::StateIndex>
where
    D: Deterministic + States,
    StateColor<D>: Color + Eq + std::hash::Hash,
{
    let start = Instant::now();
    let mut ids = crate::ts::CompactIdMap::new(mm.state_bound(), 0);
    for q in mm.states() {
        ids.get_or_insert(q);
    }
    let states = ids.states().to_vec();
    let symbols: Vec<_> = mm.symbols().collect();

    let mut classes: math::FxIndexMap<StateColor<D>, usize> = math::FxIndexMap::default();
    let initial = mm
        .states_with_color()
        .map(|(_, c)| {
            let next = classes.len();
            *classes.entry(c).or_insert(next)
        })
        .collect::<Vec<_>>();

    let mut raw = vec![Vec::new(); symbols.len()];
    for (s, sym) in symbols.iter().enumerate() {
        for (q, state) in states.iter().enumerate() {
            if let Some(t) = mm.edge(*state, *sym)
                && let Some(target) = ids.id(&t.target())
            {
                raw[s].push((target, q, 0));
            }
        }
    }
    let pre = raw
        .into_iter()
        .map(|e| Predecessors::new(states.len(), e))
        .collect();

    let block_of = refine(states.len(), 1, pre, initial);
    debug!(
        "computed greatest bisimulation for Moore machine in {} microseconds",
        start.elapsed().as_micros()
    );
    collect_partition(&states, &block_of)
}

/// Partition refinement algorithm for deterministic finite automata that have outputs on the states.
/// Runs in O(n log n) time, where n is the number of states of the automaton and returns the unique
/// minimal automaton that is bisimilar to the input. This method computes the maximal bisimulation
/// by using [`moore_greatest_bisimulation`] and then uses the partition to compute the quotient
/// automaton.
pub fn moore_partition_refinement<D>(mm: D) -> MooreMachine<DTS<D::Alphabet, D::StateColor, Void>>
where
    D: Congruence + States,
    StateColor<D>: Color + Eq + std::hash::Hash,
{
    let partition = moore_greatest_bisimulation(&mm);
    trace!(
        "Building quotient with partition {{{}}}",
        partition
            .iter()
            .map(|set| format!("{{{}}}", set.iter().map(|c| format!("{c:?}")).join(", ")))
            .join(", ")
    );

    let start = Instant::now();

    // The edge colors are irrelevant for a Moore machine. Erasing them before taking the
    // quotient avoids collecting the edge colors of every class, the quotient then only
    // carries (zero-sized) `Void` colors that are dropped when collecting.
    let moore = mm
        .erase_edge_colors()
        .quotient(partition)
        .map_state_colors(|c| {
            // assert!(c.iter().all_equal());
            c[0].clone()
        })
        .collect_moore();
    debug!(
        "Collecting into Moore machine took {} microseconds",
        start.elapsed().as_micros()
    );
    moore
}

#[cfg(test)]
mod tests {
    use super::{
        mealy_greatest_bisimulation, moore_greatest_bisimulation, moore_partition_refinement,
    };
    use crate::States;
    use crate::alphabet::CharAlphabet;
    use crate::ts::{Deterministic, ForAlphabet, Sproutable};
    use crate::{DTS, TransitionSystem, tests::wiki_dfa};

    #[test]
    fn partition_refinement_moore() {
        let dfa = wiki_dfa();

        let p = moore_partition_refinement(&dfa);
        assert_eq!(p.state_count(), 3);
        assert!(p.bisimilar(dfa));
    }

    #[test]
    fn partition_refinement_mealy() {
        let mm = DTS::builder()
            .with_transitions([
                (0, 'a', 0, 1),
                (0, 'b', 1, 0),
                (1, 'a', 0, 0),
                (1, 'b', 1, 0),
            ])
            .into_mealy(0);
        let minimized = mm.minimize();
        assert_eq!(minimized.state_count(), 1)
    }

    /// Deterministic pseudo random machines; edges are missing with some probability.
    fn random_machine(n: usize, seed: u64) -> DTS<CharAlphabet, u8, u8> {
        let mut x = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
        let mut next = move |bound: usize| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x % bound as u64) as usize
        };
        let mut ts = DTS::for_alphabet(CharAlphabet::of_size(2));
        for _ in 0..n {
            ts.add_state(next(2) as u8);
        }
        for q in 0..n {
            for sym in ['a', 'b'] {
                if next(10) > 0 {
                    ts.add_edge((q as u32, sym, next(2) as u8, next(n) as u32));
                }
            }
        }
        ts
    }

    /// Naive fixpoint computation of the coarsest partition by repeatedly comparing signatures.
    fn naive_classes(
        ts: &DTS<CharAlphabet, u8, u8>,
        use_edge_colors: bool,
    ) -> std::collections::BTreeSet<std::collections::BTreeSet<u32>> {
        let n = ts.state_count();
        let mut class: Vec<usize> = (0..n)
            .map(|q| {
                if use_edge_colors {
                    0
                } else {
                    *ts.state_color(q as u32).unwrap() as usize
                }
            })
            .collect();
        loop {
            let sig = |q: usize| {
                let succ: Vec<_> = ['a', 'b']
                    .iter()
                    .map(|&sym| {
                        ts.edge(q as u32, sym).map(|e| {
                            (
                                class[e.target() as usize],
                                use_edge_colors.then(|| *e.color()),
                            )
                        })
                    })
                    .collect();
                (class[q], succ)
            };
            let mut ids = std::collections::BTreeMap::new();
            let new: Vec<usize> = (0..n)
                .map(|q| {
                    let len = ids.len();
                    *ids.entry(sig(q)).or_insert(len)
                })
                .collect();
            let old = class
                .iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len();
            if ids.len() == old {
                break;
            }
            class = new;
        }
        let mut out = std::collections::BTreeMap::<usize, std::collections::BTreeSet<u32>>::new();
        for (q, c) in class.iter().enumerate() {
            out.entry(*c).or_default().insert(q as u32);
        }
        out.into_values().collect()
    }

    #[test]
    fn hopcroft_agrees_with_naive_refinement() {
        for seed in 0..200 {
            let n = 1 + (seed as usize % 40);
            let ts = random_machine(n, seed);
            let moore = moore_greatest_bisimulation(&ts);
            assert_eq!(
                moore
                    .iter()
                    .cloned()
                    .collect::<std::collections::BTreeSet<_>>(),
                naive_classes(&ts, false),
                "moore, seed {seed}"
            );
            let mealy = mealy_greatest_bisimulation(&ts);
            assert_eq!(
                mealy
                    .iter()
                    .cloned()
                    .collect::<std::collections::BTreeSet<_>>(),
                naive_classes(&ts, true),
                "mealy, seed {seed}"
            );
        }
    }
}
