//! Building, traversing, transforming and shrinking transition systems.

mod common;

use automata::alphabet::CharAlphabet;
use automata::representation::{CollectTs, IntoTs};
use automata::ts::operations::{MatchingProduct, ProductIndex};
use automata::ts::{
    Builder, Deterministic, ForAlphabet, PredecessorIterable, Shrinkable, Sproutable,
};
use automata::{DTS, Int, Pointed, States, TransitionSystem, Void};
use common::Dts;
use gungraun::{Dhat, prelude::*};
use std::hint::black_box;

fn scrambled(n: usize) -> Dts {
    common::scrambled(n, 2)
}
fn dfa(n: usize) -> automata::automaton::DFA {
    common::dfa(n, 2)
}
fn scrambled_k8(n: usize) -> (Dts, usize) {
    (common::scrambled(n, 8), 8)
}
fn scrambled_k2(n: usize) -> (Dts, usize) {
    (common::scrambled(n, 2), 2)
}
fn nth_from_end(n: usize) -> automata::NTS<CharAlphabet, bool, Void> {
    common::nth_from_end(n)
}

// ---- building step by step -----------------------------------------------------------------

/// All edges of `scrambled(n, k)` as a list, in the order of the states.
fn edge_list(n: usize, k: usize) -> (usize, usize, Vec<(u32, char, u32)>) {
    let ts = common::scrambled(n, k);
    let edges = ts
        .states()
        .flat_map(|q| {
            let ts = &ts;
            common::symbols(k)
                .into_iter()
                .filter_map(move |c| ts.successor(q, c).map(|p| (q, c, p)))
        })
        .collect();
    (n, k, edges)
}

fn reversed_edge_list(n: usize, k: usize) -> (usize, usize, Vec<(u32, char, u32)>) {
    let (n, k, mut edges) = edge_list(n, k);
    edges.reverse();
    (n, k, edges)
}

fn add_edges(n: usize, k: usize, edges: &[(u32, char, u32)]) -> Dts {
    let mut ts = DTS::<CharAlphabet, bool, Void>::for_alphabet(CharAlphabet::of_size(k));
    for q in 0..n {
        ts.add_state(q % 3 == 0);
    }
    for &edge in edges {
        ts.add_edge(edge);
    }
    ts
}

#[library_benchmark]
#[bench::k2_5000(args = (5_000, 2), setup = edge_list)]
#[bench::k8_5000(args = (5_000, 8), setup = edge_list)]
fn add_edges_in_order((n, k, edges): (usize, usize, Vec<(u32, char, u32)>)) -> Dts {
    add_edges(n, k, &edges)
}

#[library_benchmark]
#[bench::k2_5000(args = (5_000, 2), setup = reversed_edge_list)]
fn add_edges_in_reverse((n, k, edges): (usize, usize, Vec<(u32, char, u32)>)) -> Dts {
    add_edges(n, k, &edges)
}

#[library_benchmark]
#[bench::k2_5000(args = (5_000, 2), setup = edge_list)]
fn builder_with_edges((n, _k, edges): (usize, usize, Vec<(u32, char, u32)>)) -> Dts {
    Builder::without_edge_colors()
        .with_state_colors((0..n).map(|q| q % 3 == 0))
        .with_edges(edges)
        .build_dts()
}

// ---- lookups ---------------------------------------------------------------------------------

#[library_benchmark]
#[bench::scrambled_2000(args = (2_000), setup = scrambled_k2)]
#[bench::scrambled_k8_2000(args = (2_000), setup = scrambled_k8)]
fn successor_index_all_pairs((ts, k): (Dts, usize)) -> u64 {
    let symbols = common::symbols(k);
    let mut sum = 0u64;
    for q in ts.states() {
        for &c in &symbols {
            sum += ts.successor(q, c).unwrap_or(0) as u64;
        }
    }
    black_box(sum)
}

#[library_benchmark]
#[bench::scrambled_2000(args = (2_000), setup = scrambled_k2)]
#[bench::scrambled_k8_2000(args = (2_000), setup = scrambled_k8)]
fn edges_from_all_states((ts, _k): (Dts, usize)) -> usize {
    black_box(
        ts.states()
            .map(|q| ts.edges_from(q).map_or(0, |e| e.count()))
            .sum(),
    )
}

type ProductQueries = (Dts, Dts, Vec<(ProductIndex<u32, u32>, char)>);

fn product_queries(n: usize) -> ProductQueries {
    let (l, r) = (common::scrambled(n, 2), common::counter(n, 2));
    let queries = (0..1_000)
        .map(|i| {
            (
                ProductIndex(((i * 37) % n) as u32, ((i * 101 + 5) % n) as u32),
                ['a', 'b'][i % 2],
            )
        })
        .collect();
    (l, r, queries)
}

#[library_benchmark]
#[bench::n200(args = (200), setup = product_queries)]
fn matching_product_successor_index((l, r, queries): ProductQueries) -> usize {
    let product = MatchingProduct(&l, &r);
    black_box(
        queries
            .iter()
            .filter(|&&(q, c)| product.successor(q, c).is_some())
            .count(),
    )
}

// ---- traversal -------------------------------------------------------------------------------

#[library_benchmark]
#[bench::scrambled_2000(args = (2_000), setup = scrambled)]
#[bench::scrambled_8000(args = (8_000), setup = scrambled)]
fn reachable_states(ts: Dts) -> usize {
    black_box(ts.reachable_state_indices_from(0).count())
}

#[library_benchmark]
#[bench::scrambled_2000(args = (2_000), setup = dfa)]
#[bench::scrambled_8000(args = (8_000), setup = dfa)]
fn minimal_representatives(ts: automata::automaton::DFA) -> usize {
    black_box(ts.minimal_representatives_iter().count())
}

fn small_cycles_dfa(n: usize) -> automata::automaton::DFA {
    use automata::representation::IntoTs;
    common::small_cycles(n).into_dfa_with_initial(0)
}

// The representative of every SCC (used for witnesses, e.g. of a DPA). Chains of 4-cycles give
// n / 4 components, each of which is farther from the initial state than the previous one.
#[library_benchmark]
#[bench::small_cycles_100(args = (100), setup = small_cycles_dfa)]
#[bench::small_cycles_400(args = (400), setup = small_cycles_dfa)]
fn scc_minimal_representatives(ts: automata::automaton::DFA) -> usize {
    let sccs = ts.sccs();
    black_box(
        sccs.iter()
            .filter(|(_, scc)| scc.minimal_representative().is_some())
            .count(),
    )
}

// The representative of each state looked up on its own.
#[library_benchmark]
#[bench::scrambled_100(args = (100), setup = dfa)]
#[bench::scrambled_300(args = (300), setup = dfa)]
fn minimal_representative_of_all_states(ts: automata::automaton::DFA) -> usize {
    black_box(
        ts.states()
            .filter(|&q| ts.minimal_representative(q).is_some())
            .count(),
    )
}

#[library_benchmark]
#[bench::scrambled_500(args = (500), setup = dfa)]
#[bench::scrambled_1500(args = (1_500), setup = dfa)]
fn canonical_naming(ts: automata::automaton::DFA) -> usize {
    black_box(ts.canonical_naming().len())
}

#[library_benchmark]
#[bench::scrambled_2000(args = (2_000), setup = scrambled)]
#[bench::scrambled_8000(args = (8_000), setup = scrambled)]
fn predecessors_of_all_states(ts: Dts) -> usize {
    black_box(
        ts.states()
            .map(|q| ts.predecessors(q).map_or(0, |p| p.count()))
            .sum(),
    )
}

// ---- collecting and mapping --------------------------------------------------------------------

#[library_benchmark]
#[bench::scrambled_10000(args = (10_000), setup = scrambled)]
#[bench::scrambled_40000(args = (40_000), setup = scrambled)]
fn clone(ts: Dts) -> Dts {
    black_box(ts.clone())
}

#[library_benchmark]
#[bench::scrambled_10000(args = (10_000), setup = scrambled)]
#[bench::scrambled_40000(args = (40_000), setup = scrambled)]
fn collect_dts(ts: Dts) -> Dts {
    black_box(ts.collect_dts())
}

#[library_benchmark]
#[bench::scrambled_10000(args = (10_000), setup = scrambled)]
#[bench::scrambled_40000(args = (40_000), setup = scrambled)]
fn map_edge_colors_collect(ts: Dts) -> DTS<CharAlphabet, bool, Int> {
    black_box(ts.map_edge_colors(|_| 0 as Int).collect_dts())
}

#[library_benchmark]
#[bench::scrambled_10000(args = (10_000), setup = scrambled)]
fn erase_state_colors_collect(ts: Dts) -> DTS<CharAlphabet, Void, Void> {
    black_box(ts.erase_state_colors().collect_dts())
}

#[library_benchmark]
#[bench::scrambled_10000(args = (10_000), setup = scrambled)]
fn into_dfa(ts: Dts) -> automata::automaton::DFA {
    black_box(ts.into_dfa_with_initial(0))
}

// ---- shrinking ---------------------------------------------------------------------------------

#[library_benchmark]
#[bench::scrambled_10000(args = (10_000), setup = scrambled)]
#[bench::scrambled_40000(args = (40_000), setup = scrambled)]
fn remove_edges_from_matching(mut ts: Dts) -> Dts {
    let n = ts.state_count();
    for i in 0..1_000 {
        black_box(ts.remove_edges_from_matching((i * (n / 1_000)) as u32, 'a'));
    }
    ts
}

#[library_benchmark]
#[bench::scrambled_10000(args = (10_000), setup = scrambled)]
#[bench::scrambled_40000(args = (40_000), setup = scrambled)]
fn remove_state(mut ts: Dts) -> Dts {
    let n = ts.state_count();
    for i in 0..1_000 {
        black_box(ts.remove_state((i * (n / 1_000)) as u32));
    }
    ts
}

// ---- subset construction ---------------------------------------------------------------------

#[library_benchmark]
#[bench::nth_from_end_8(args = (8), setup = nth_from_end)]
#[bench::nth_from_end_10(args = (10), setup = nth_from_end)]
#[bench::nth_from_end_12(args = (12), setup = nth_from_end)]
fn subset_construction(nts: automata::NTS<CharAlphabet, bool, Void>) -> usize {
    black_box(
        nts.with_initial(0)
            .subset_construction()
            .reachable_part()
            .collect_dts()
            .state_count(),
    )
}

library_benchmark_group!(
    name = ts;
    benchmarks = add_edges_in_order, add_edges_in_reverse, builder_with_edges,
        successor_index_all_pairs, edges_from_all_states, matching_product_successor_index,
        reachable_states, minimal_representatives, scc_minimal_representatives,
        minimal_representative_of_all_states, canonical_naming, predecessors_of_all_states,
        clone, collect_dts, map_edge_colors_collect, erase_state_colors_collect, into_dfa,
        remove_edges_from_matching, remove_state, subset_construction
);

main!(
    config = LibraryBenchmarkConfig::default().tool(Dhat::default()),
    library_benchmark_groups = ts
);
