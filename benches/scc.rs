//! Strongly connected component decompositions on graphs of different shapes.

mod common;

use automata::TransitionSystem;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

const SIZES: [usize; 3] = [100, 1_000, 5_000];

fn bench_family(
    c: &mut Criterion,
    name: &str,
    make: impl Fn(usize) -> automata::DTS<automata::alphabet::CharAlphabet, bool, automata::Void>,
) {
    let mut group = c.benchmark_group(format!("scc/{name}"));
    for n in SIZES {
        let ts = make(n);
        group.bench_with_input(BenchmarkId::new("tarjan_iterative", n), &ts, |b, ts| {
            b.iter(|| black_box(ts.sccs().size()))
        });
        group.bench_with_input(BenchmarkId::new("tarjan_recursive", n), &ts, |b, ts| {
            b.iter(|| black_box(ts.sccs_recursive().size()))
        });
        // Kosaraju is quadratic (see the issue about it), 5000 states take minutes
        if n <= 1_000 {
            group.bench_with_input(BenchmarkId::new("kosaraju", n), &ts, |b, ts| {
                b.iter(|| black_box(ts.sccs_kosaraju(0).size()))
            });
        }
    }
    group.finish();
}

fn sccs(c: &mut Criterion) {
    bench_family(c, "random", |n| common::random_dts(n, 42));
    bench_family(c, "ring", common::ring);
    bench_family(c, "back_edges", common::back_edges);
    bench_family(c, "path", common::path);
    bench_family(c, "small_cycles", common::small_cycles);
}

criterion_group!(benches, sccs);
criterion_main!(benches);
