//! Common operations on transition systems and DFAs.

mod common;

use automata::TransitionSystem;
use automata::automaton::DFA;
use automata::representation::{CollectTs, IntoTs};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

fn dfa(n: usize, seed: u64) -> DFA {
    common::random_dts(n, seed).into_dfa_with_initial(0)
}

fn reachability(c: &mut Criterion) {
    let mut group = c.benchmark_group("reachability");
    for n in [1_000, 10_000, 100_000] {
        let ts = common::random_dts(n, 1);
        group.bench_with_input(BenchmarkId::new("reachable_states", n), &ts, |b, ts| {
            b.iter(|| black_box(ts.reachable_state_indices_from(0).count()))
        });
        group.bench_with_input(BenchmarkId::new("collect_dts", n), &ts, |b, ts| {
            b.iter(|| black_box(ts.collect_dts()))
        });
    }
    for n in [1_000, 10_000] {
        let dfa = dfa(n, 2);
        group.bench_with_input(
            BenchmarkId::new("minimal_representatives", n),
            &dfa,
            |b, dfa| b.iter(|| black_box(dfa.minimal_representatives_iter().count())),
        );
    }
    group.finish();
}

fn dfa_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("dfa");
    for n in [50, 200, 1_000, 5_000, 20_000] {
        let a = dfa(n, 3);
        group.bench_with_input(BenchmarkId::new("minimize", n), &a, |b, a| {
            b.iter(|| black_box(a.clone().minimize().size()))
        });
    }
    for n in [50, 200, 1_000] {
        let (a, b) = (dfa(n, 4), dfa(n, 5));
        group.bench_with_input(
            BenchmarkId::new("intersection_is_empty", n),
            &(a.clone(), b.clone()),
            |bench, (a, b)| bench.iter(|| black_box(a.intersection_is_empty(b))),
        );
        group.bench_with_input(
            BenchmarkId::new("intersection_materialized", n),
            &(a.clone(), b.clone()),
            |bench, (a, b)| bench.iter(|| black_box(a.intersection(b).is_empty_language())),
        );
        group.bench_with_input(
            BenchmarkId::new("equivalent", n),
            &(a, b),
            |bench, (a, b)| bench.iter(|| black_box(a.equivalent(b))),
        );
    }
    // equal languages force the search to visit the whole (diagonal of the) product
    for n in [50, 200, 1_000, 5_000] {
        let a = dfa(n, 6);
        group.bench_with_input(
            BenchmarkId::new("equivalent_identical", n),
            &(a.clone(), a),
            |bench, (a, b)| bench.iter(|| black_box(a.equivalent(b))),
        );
    }
    group.finish();
}

fn subset_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("subset_construction");
    group.sample_size(20);
    for n in [8, 12, 16] {
        let nts = common::random_nts(n, 2, 6);
        group.bench_with_input(BenchmarkId::from_parameter(n), &nts, |b, nts| {
            b.iter(|| {
                black_box(
                    nts.clone()
                        .with_initial(0)
                        .subset_construction()
                        .collect_dts()
                        .size(),
                )
            })
        });
    }
    group.finish();
}

criterion_group!(benches, reachability, dfa_operations, subset_construction);
criterion_main!(benches);
