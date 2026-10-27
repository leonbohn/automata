//! Baseline benchmarks for the performance problems tracked in the 0.2 redesign (see #30 and #32).
//!
//! Every benchmark here only uses public API and deterministic inputs, so that numbers are
//! comparable between commits, and so that the benchmarks survive the API redesign with only
//! mechanical updates. Heavy benchmarks use a small sample size; run `cargo bench --bench
//! baseline -- --quick` for a fast pass.

mod common;

use automata::representation::CollectTs;
use automata::ts::operations::MatchingProduct;
use automata::ts::{Deterministic, Shrinkable, TransitionSystem};
use automata::{Int, upw};
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

/// P1: subset construction where all `2^n` subsets are reachable.
fn subset_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("baseline/subset_construction");
    group.sample_size(10);
    for n in [8, 10, 12, 13, 14] {
        let nts = common::nth_from_end(n);
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

/// P2: normalization of random parity automata.
fn dpa_normalized(c: &mut Criterion) {
    let mut group = c.benchmark_group("baseline/dpa_normalized");
    group.sample_size(10);
    for n in [2_000, 8_000, 32_000] {
        let dpa = common::dpa(n, 7);
        group.bench_with_input(BenchmarkId::from_parameter(n), &dpa, |b, dpa| {
            b.iter(|| black_box(dpa.normalized().size()))
        });
    }
    group.finish();
}

/// P3: removing the outgoing edges of many states. Two edges per state, so `E = 2n`.
fn edge_removal(c: &mut Criterion) {
    let mut group = c.benchmark_group("baseline/remove_edges_from_matching_x1000");
    group.sample_size(10);
    for edges in [20_000, 200_000] {
        let n = edges / 2;
        let ts = common::random_dts(n, 8);
        group.bench_with_input(BenchmarkId::from_parameter(edges), &ts, |b, ts| {
            b.iter_batched_ref(
                || ts.clone(),
                |ts| {
                    for i in 0..1_000 {
                        black_box(ts.remove_edges_from_matching((i * (n / 1_000)) as u32, 'a'));
                    }
                },
                BatchSize::LargeInput,
            )
        });
    }
    group.finish();
}

/// P4: cloning versus collecting a transition system.
fn collect(c: &mut Criterion) {
    let mut group = c.benchmark_group("baseline/collect");
    group.sample_size(10);
    for n in [100_000, 1_000_000] {
        let ts = common::random_dts(n, 9);
        group.bench_with_input(BenchmarkId::new("clone", n), &ts, |b, ts| {
            b.iter(|| black_box(ts.clone()))
        });
        group.bench_with_input(BenchmarkId::new("collect_dts", n), &ts, |b, ts| {
            b.iter(|| black_box(ts.collect_dts()))
        });
        group.bench_with_input(
            BenchmarkId::new("map_edge_colors_collect_dts", n),
            &ts,
            |b, ts| b.iter(|| black_box(ts.map_edge_colors(|_| 0 as Int).collect_dts())),
        );
    }
    group.finish();
}

/// P5: `successor_index` on a product, which calls the default `contains_state_index`.
fn product_successor_index(c: &mut Criterion) {
    let mut group = c.benchmark_group("baseline/matching_product_successor_index_x1000");
    for n in [100, 400] {
        let (l, r) = (common::random_dts(n, 10), common::random_dts(n, 11));
        let product = MatchingProduct(&l, &r);
        let mut rng = common::Rng::new(12);
        let queries: Vec<_> = (0..1_000)
            .map(|_| {
                (
                    automata::ts::operations::ProductIndex(
                        rng.below(n) as u32,
                        rng.below(n) as u32,
                    ),
                    ['a', 'b'][rng.below(2)],
                )
            })
            .collect();
        group.bench_with_input(
            BenchmarkId::from_parameter(n * n),
            &queries,
            |b, queries| {
                b.iter(|| {
                    for &(state, sym) in queries {
                        black_box(product.successor_index(state, sym));
                    }
                })
            },
        );
    }
    group.finish();
}

/// Baseline for the run machinery: finite words on a DFA, ultimately periodic words on a DPA.
fn run_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("baseline/accepts_x1000");
    let dfa = {
        use automata::representation::IntoTs;
        common::random_dts(1_000, 13).into_dfa_with_initial(0)
    };
    let words = common::random_words(1_000, 2, 50, 200, 14);
    group.bench_function("dfa_finite_words", |b| {
        b.iter(|| {
            for w in &words {
                black_box(dfa.accepts(w.as_str()));
            }
        })
    });

    let dpa = common::dpa(1_000, 15);
    let bases = common::random_words(1_000, 2, 0, 50, 16);
    let cycles = common::random_words(1_000, 2, 1, 50, 17);
    group.bench_function("dpa_ultimately_periodic_words", |b| {
        b.iter(|| {
            for (base, cycle) in bases.iter().zip(&cycles) {
                black_box(dpa.accepts(upw!(base.as_str(), cycle.as_str())));
            }
        })
    });
    group.finish();
}

/// Edge insertion and lookup on a deterministic TS, over two and over eight symbols.
fn edge_insertion_and_lookup(c: &mut Criterion) {
    use automata::alphabet::CharAlphabet;
    use automata::ts::{ForAlphabet, Sproutable};
    use automata::{DTS, Void};

    const N: usize = 20_000;
    let mut group = c.benchmark_group("baseline/edges");
    group.sample_size(20);
    for k in [2, 8] {
        let symbols = common::symbols(k);
        let mut rng = common::Rng::new(18);
        let targets: Vec<u32> = (0..N * k).map(|_| rng.below(N) as u32).collect();

        group.bench_function(BenchmarkId::new("insert", k), |b| {
            b.iter(|| {
                let mut ts =
                    DTS::<CharAlphabet, bool, Void>::for_alphabet(CharAlphabet::of_size(k));
                for _ in 0..N {
                    ts.add_state(false);
                }
                for q in 0..N {
                    for (i, &sym) in symbols.iter().enumerate() {
                        ts.add_edge((q as u32, sym, targets[q * k + i]));
                    }
                }
                black_box(ts)
            })
        });

        let ts = common::random_dts_over(N, k, 19);
        group.bench_function(BenchmarkId::new("lookup", k), |b| {
            b.iter(|| {
                for q in 0..N as u32 {
                    for &sym in &symbols {
                        black_box(ts.successor_index(q, sym));
                    }
                }
            })
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    subset_construction,
    dpa_normalized,
    edge_removal,
    collect,
    product_successor_index,
    run_throughput,
    edge_insertion_and_lookup
);
criterion_main!(benches);
