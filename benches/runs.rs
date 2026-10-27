//! Runs of finite and infinite words, and what is computed from them.

mod common;

use automata::automaton::{DFA, DPA};
use automata::{Deterministic, TransitionSystem, upw};
use common::FixtureDpa;
use gungraun::{Dhat, prelude::*};
use std::hint::black_box;

// ---- finite words ------------------------------------------------------------------------------

fn dfa_with_word(len: usize) -> (DFA, Vec<char>) {
    (
        common::dfa(1_000, 2),
        common::word(len, 2).chars().collect(),
    )
}

fn dfa_with_words(count: usize) -> (DFA, Vec<String>) {
    let words = (0..count).map(|i| common::word(50 + i % 150, 2)).collect();
    (common::dfa(1_000, 2), words)
}

// One long word: the cost per step, without the per-call overhead.
#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::len_100(args = (100), setup = dfa_with_word)]
#[bench::len_10000(args = (10_000), setup = dfa_with_word)]
#[bench::len_100000(args = (100_000), setup = dfa_with_word)]
fn dfa_accepts_one_word((dfa, word): (DFA, Vec<char>)) -> bool {
    black_box(dfa.accepts(word.as_slice()))
}

// Many short words: the per-call overhead.
#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::count_1000(args = (1_000), setup = dfa_with_words)]
fn dfa_accepts_many_words((dfa, words): (DFA, Vec<String>)) -> usize {
    black_box(words.iter().filter(|w| dfa.accepts(w.as_str())).count())
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::count_1000(args = (1_000), setup = dfa_with_words)]
fn dfa_reached_state((dfa, words): (DFA, Vec<String>)) -> u64 {
    black_box(
        words
            .iter()
            .map(|w| dfa.reached_state_index(w.as_str()).unwrap_or(0) as u64)
            .sum(),
    )
}

// ---- infinite words ----------------------------------------------------------------------------

fn dpa_with_lassos(spoke: usize, cycle: usize) -> (DPA, Vec<(String, String)>) {
    (
        common::scrambled_dpa(1_000, 2, 8),
        common::lassos(50, 2, spoke, cycle),
    )
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::short(args = (5, 10), setup = dpa_with_lassos)]
#[bench::long(args = (500, 1_000), setup = dpa_with_lassos)]
fn dpa_accepts_lassos((dpa, lassos): (DPA, Vec<(String, String)>)) -> usize {
    black_box(
        lassos
            .iter()
            .filter(|(u, v)| dpa.accepts(upw!(u.as_str(), v.as_str())))
            .count(),
    )
}

// The infinity set of a run: the priorities seen infinitely often.
#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::short(args = (5, 10), setup = dpa_with_lassos)]
#[bench::long(args = (500, 1_000), setup = dpa_with_lassos)]
fn dpa_recurrent_edge_colors((dpa, lassos): (DPA, Vec<(String, String)>)) -> usize {
    black_box(
        lassos
            .iter()
            .filter_map(|(u, v)| dpa.recurrent_edge_colors(upw!(u.as_str(), v.as_str())))
            .map(|colors| colors.len())
            .sum(),
    )
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::short(args = (5, 10), setup = dpa_with_lassos)]
#[bench::long(args = (500, 1_000), setup = dpa_with_lassos)]
fn dpa_recurrent_states((dpa, lassos): (DPA, Vec<(String, String)>)) -> usize {
    black_box(
        lassos
            .iter()
            .filter_map(|(u, v)| dpa.recurrent_state_indices(upw!(u.as_str(), v.as_str())))
            .map(|states| states.len())
            .sum(),
    )
}

// The whole sequence of visited states and of edge colors along the prefix `u v v v`.
#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::short(args = (5, 10), setup = dpa_with_lassos)]
#[bench::long(args = (500, 1_000), setup = dpa_with_lassos)]
fn dpa_visited_sequences((dpa, lassos): (DPA, Vec<(String, String)>)) -> usize {
    black_box(
        lassos
            .iter()
            .map(|(u, v)| {
                let w: Vec<char> = format!("{u}{v}{v}{v}").chars().collect();
                dpa.visited_state_sequence(w.as_slice())
                    .map_or(0, |s| s.len())
                    + dpa.visited_edge_colors(w.as_slice()).map_or(0, |s| s.len())
            })
            .sum(),
    )
}

// ---- infinite words on the fixtures ------------------------------------------------------------

fn lassos_over(
    dpa: &FixtureDpa,
    count: usize,
) -> Vec<
    automata::word::ReducedOmegaWord<
        <automata::alphabet::PropAlphabet as automata::alphabet::Alphabet>::Symbol,
    >,
> {
    (0..count)
        .map(|i| common::fixture_lasso(dpa.alphabet(), 3 + i % 11, 2 + i % 7))
        .collect()
}

// Every fixture is run on 100 lassos. No heap profile here: parsing the fixtures is slow under DHAT.
// Every fixture is run on 100 lassos, the number of acceptances is the (checked) result.
#[library_benchmark]
#[bench::ltl(setup = common::ltl_dpas)]
#[bench::synthetic(setup = common::synthetic_dpas)]
fn fixture_accepts_lassos(dpas: Vec<FixtureDpa>) -> usize {
    black_box(
        dpas.iter()
            .map(|dpa| {
                lassos_over(dpa, 100)
                    .into_iter()
                    .filter(|w| dpa.accepts(w.clone()))
                    .count()
            })
            .sum(),
    )
}

library_benchmark_group!(
    name = runs;
    benchmarks = dfa_accepts_one_word, dfa_accepts_many_words, dfa_reached_state,
        dpa_accepts_lassos, dpa_recurrent_edge_colors, dpa_recurrent_states,
        dpa_visited_sequences, fixture_accepts_lassos
);

main!(library_benchmark_groups = runs);
