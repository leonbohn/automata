//! Strongly connected component decompositions on graphs of different shapes.

mod common;

use common::Dts;
use gungraun::{Dhat, prelude::*};
use std::hint::black_box;

fn ring(n: usize) -> Dts {
    common::ring(n)
}
fn back_edges(n: usize) -> Dts {
    common::back_edges(n)
}
fn path(n: usize) -> Dts {
    common::path(n)
}
fn small_cycles(n: usize) -> Dts {
    common::small_cycles(n)
}
fn binary_tree(n: usize) -> Dts {
    common::binary_tree(n)
}
fn grid(n: usize) -> Dts {
    common::grid(n, 32)
}
fn scrambled(n: usize) -> Dts {
    common::scrambled(n, 2)
}
fn fragmented(n: usize) -> Dts {
    common::fragmented(n, 2)
}

// Iterative Tarjan, the algorithm behind `sccs`.
#[library_benchmark]
#[bench::ring_1000(args = (1_000), setup = ring)]
#[bench::ring_4000(args = (4_000), setup = ring)]
#[bench::back_edges_1000(args = (1_000), setup = back_edges)]
#[bench::back_edges_4000(args = (4_000), setup = back_edges)]
#[bench::path_1000(args = (1_000), setup = path)]
#[bench::path_4000(args = (4_000), setup = path)]
#[bench::small_cycles_1000(args = (1_000), setup = small_cycles)]
#[bench::small_cycles_4000(args = (4_000), setup = small_cycles)]
#[bench::binary_tree_1000(args = (1_000), setup = binary_tree)]
#[bench::binary_tree_4000(args = (4_000), setup = binary_tree)]
#[bench::grid_1024(args = (1_024), setup = grid)]
#[bench::grid_4096(args = (4_096), setup = grid)]
#[bench::scrambled_1000(args = (1_000), setup = scrambled)]
#[bench::scrambled_4000(args = (4_000), setup = scrambled)]
#[bench::fragmented_1000(args = (1_000), setup = fragmented)]
#[bench::fragmented_4000(args = (4_000), setup = fragmented)]
fn tarjan(ts: Dts) -> usize {
    black_box(ts.sccs().size())
}

// The recursive variant, only on shapes where it does not overflow the stack (#23).
use automata::States;
#[library_benchmark]
#[bench::ring_1000(args = (1_000), setup = ring)]
#[bench::small_cycles_1000(args = (1_000), setup = small_cycles)]
#[bench::small_cycles_4000(args = (4_000), setup = small_cycles)]
#[bench::binary_tree_1000(args = (1_000), setup = binary_tree)]
#[bench::binary_tree_4000(args = (4_000), setup = binary_tree)]
#[bench::scrambled_1000(args = (1_000), setup = scrambled)]
#[bench::scrambled_4000(args = (4_000), setup = scrambled)]
#[bench::fragmented_1000(args = (1_000), setup = fragmented)]
#[bench::fragmented_4000(args = (4_000), setup = fragmented)]
fn tarjan_recursive(ts: Dts) -> usize {
    black_box(ts.sccs_recursive().size())
}

#[library_benchmark]
#[bench::ring_1000(args = (1_000), setup = ring)]
#[bench::ring_4000(args = (4_000), setup = ring)]
#[bench::path_1000(args = (1_000), setup = path)]
#[bench::path_4000(args = (4_000), setup = path)]
#[bench::small_cycles_1000(args = (1_000), setup = small_cycles)]
#[bench::small_cycles_4000(args = (4_000), setup = small_cycles)]
#[bench::binary_tree_1000(args = (1_000), setup = binary_tree)]
#[bench::binary_tree_4000(args = (4_000), setup = binary_tree)]
#[bench::scrambled_1000(args = (1_000), setup = scrambled)]
#[bench::scrambled_4000(args = (4_000), setup = scrambled)]
#[bench::fragmented_1000(args = (1_000), setup = fragmented)]
#[bench::fragmented_4000(args = (4_000), setup = fragmented)]
fn kosaraju(ts: Dts) -> usize {
    black_box(ts.sccs_kosaraju(0).size())
}

/// Using the result: classify every SCC, as algorithms on top of the decomposition do.
fn sccs_of_small_cycles(n: usize) -> (Dts, usize) {
    (common::small_cycles(n), n)
}

#[library_benchmark]
#[bench::small_cycles_1000(args = (1_000), setup = sccs_of_small_cycles)]
#[bench::small_cycles_4000(args = (4_000), setup = sccs_of_small_cycles)]
fn scc_queries((ts, _n): (Dts, usize)) -> usize {
    let sccs = ts.sccs();
    black_box(sccs.iter().filter(|(_, scc)| scc.size() > 1).count())
}

library_benchmark_group!(
    name = scc;
    benchmarks = tarjan, tarjan_recursive, kosaraju, scc_queries
);

main!(
    config = LibraryBenchmarkConfig::default().tool(Dhat::default()),
    library_benchmark_groups = scc
);
