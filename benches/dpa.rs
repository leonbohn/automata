//! Operations on deterministic parity automata.

mod common;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use automata::TransitionSystem;

fn normalization(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpa/normalized");
    for n in [1_000, 4_000, 16_000] {
        let dpa = common::dpa(n, 21);
        group.bench_with_input(BenchmarkId::from_parameter(n), &dpa, |b, dpa| {
            b.iter(|| black_box(dpa.normalized().size()))
        });
    }
    group.finish();
}

fn complement(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpa/complement");
    for n in [1_000, 4_000, 16_000] {
        let dpa = common::dpa(n, 22);
        group.bench_with_input(BenchmarkId::new("normalizing", n), &dpa, |b, dpa| {
            b.iter(|| black_box(dpa.clone().complement().size()))
        });
        group.bench_with_input(
            BenchmarkId::new("without_normalizing", n),
            &dpa,
            |b, dpa| {
                b.iter(|| {
                    black_box(
                        dpa.clone()
                            .complement_without_normalizing()
                            .map(|d| d.size()),
                    )
                })
            },
        );
    }
    group.finish();
}

fn witnesses(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpa/witness");
    for n in [100, 400, 1_600] {
        let dpa = common::dpa(n, 23);
        group.bench_with_input(BenchmarkId::new("accepted_word", n), &dpa, |b, dpa| {
            b.iter(|| black_box(dpa.give_accepted_word()))
        });
        group.bench_with_input(BenchmarkId::new("rejected_word", n), &dpa, |b, dpa| {
            b.iter(|| black_box(dpa.give_rejected_word()))
        });
    }
    group.finish();
}

fn comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpa/compare");
    group.sample_size(20);
    for n in [10, 25, 50] {
        let (a, b) = (common::dpa(n, 24), common::dpa(n, 25));
        group.bench_with_input(
            BenchmarkId::new("language_equivalent_random", n),
            &(a.clone(), b.clone()),
            |bench, (a, b)| bench.iter(|| black_box(a.language_equivalent(b))),
        );
        group.bench_with_input(
            BenchmarkId::new("included_in_random", n),
            &(a.clone(), b.clone()),
            |bench, (a, b)| bench.iter(|| black_box(a.included_in(b))),
        );
        // equal languages cannot be refuted early, so every pair of colors is searched
        let normalized = a.normalized();
        group.bench_with_input(
            BenchmarkId::new("language_equivalent_normalized", n),
            &(a.clone(), normalized),
            |bench, (a, norm)| bench.iter(|| black_box(a.language_equivalent(norm))),
        );
    }
    group.finish();
}

criterion_group!(benches, normalization, complement, witnesses, comparison);
criterion_main!(benches);
