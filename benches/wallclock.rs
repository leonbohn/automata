//! Wall-clock times of a few representative operations.
//!
//! These numbers depend on the machine and are never compared automatically; they exist to
//! show real magnitudes next to the instruction counts of the other targets (the benchmark
//! service lists them in the detail view of a run only). Same inputs as the other targets,
//! just fewer of them.

mod common;

use automata::ts::Sccs;
use automata::{
    DTS, Int, Pointed, States, TransitionSystem, Void, alphabet::CharAlphabet,
    representation::IntoTransitions,
};
use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

fn operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("wallclock");
    group.sample_size(20);

    let ts = common::scrambled(10_000, 2);
    group.bench_function("scc/tarjan/scrambled_10000", |b| {
        b.iter(|| black_box(Sccs::on(&ts).compute().size()))
    });

    let dpa = common::scrambled_dpa(4_000, 2, 8);
    group.bench_function("dpa/normalized/scrambled_4000", |b| {
        b.iter(|| black_box(dpa.normalized().state_count()))
    });
    group.bench_function("dpa/complement/scrambled_4000", |b| {
        b.iter(|| black_box(dpa.clone().complement().state_count()))
    });

    let dfa = common::redundant_dfa(4_000, 2);
    group.bench_function("dfa/minimize/redundant_4000", |b| {
        b.iter(|| black_box(dfa.clone().minimize().state_count()))
    });

    let word: Vec<char> = common::word(100_000, 2).chars().collect();
    let dfa = common::dfa(1_000, 2);
    group.bench_function("dfa/accepts/word_100000", |b| {
        b.iter(|| black_box(dfa.accepts(word.as_slice())))
    });

    let nts = common::nth_from_end(12);
    group.bench_function("nfa/subset_construction/nth_from_end_12", |b| {
        b.iter(|| {
            black_box(
                nts.clone()
                    .with_initial(0)
                    .subset_construction()
                    .reachable_part()
                    .collect::<DTS<CharAlphabet, Vec<bool>, Vec<Void>>>()
                    .state_count(),
            )
        })
    });

    let texts = common::fixture_texts(common::LTL);
    group.bench_function("hoa/parse/ltl", |b| {
        b.iter(|| {
            black_box(
                texts
                    .iter()
                    .map(|t| common::parse_dpa(t).state_count())
                    .sum::<usize>(),
            )
        })
    });
    group.finish();
}

fn collecting(c: &mut Criterion) {
    use criterion::BatchSize::LargeInput;
    let mut group = c.benchmark_group("collect");
    group.sample_size(10);
    for n in [100_000, 1_000_000] {
        let ts = common::scrambled(n, 2);
        group.bench_function(format!("clone/{n}"), |b| {
            b.iter_batched(|| ts.clone(), |ts| black_box(ts.clone()), LargeInput)
        });
        group.bench_function(format!("collect_owned/{n}"), |b| {
            b.iter_batched(
                || ts.clone(),
                |ts| black_box(ts.collect::<DTS<CharAlphabet, bool, Void>>()),
                LargeInput,
            )
        });
        group.bench_function(format!("collect_ref/{n}"), |b| {
            b.iter(|| black_box((&ts).collect::<DTS<CharAlphabet, bool, Void>>()))
        });
        group.bench_function(format!("map_edge_colors_collect_owned/{n}"), |b| {
            b.iter_batched(
                || ts.clone(),
                |ts| {
                    black_box(
                        ts.map_edge_colors(|_| 0 as Int)
                            .collect::<DTS<CharAlphabet, bool, Int>>(),
                    )
                },
                LargeInput,
            )
        });
    }
    group.finish();
}

criterion_group!(benches, operations, collecting);
criterion_main!(benches);
