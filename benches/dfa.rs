//! Operations on deterministic finite automata and Moore machines.

mod common;

use automata::TransitionSystem;
use automata::alphabet::CharAlphabet;
use automata::automaton::{DFA, MooreMachine};
use automata::representation::CollectTs;
use gungraun::prelude::*;
use std::hint::black_box;

fn scrambled(n: usize) -> DFA {
    common::dfa(n, 2)
}
fn counter(n: usize) -> DFA {
    common::counter_dfa(n, 2)
}
fn redundant(n: usize) -> DFA {
    common::redundant_dfa(n, 2)
}

// Two different automata of the same size.
fn two_scrambled(n: usize) -> (DFA, DFA) {
    (common::dfa(n, 2), common::counter_dfa(n, 2))
}

// An automaton and a smaller one with the same language: nothing can be refuted, so the
// whole product is searched.
fn with_minimized(n: usize) -> (DFA, DFA) {
    let dfa = common::redundant_dfa(n, 2);
    let minimized = dfa.clone().minimize();
    (dfa, minimized)
}

// Two automata that differ only on words which lead to the far end of the counter.
fn deep_difference(n: usize) -> (DFA, DFA) {
    (
        common::counter_dfa(n, 2),
        common::counter_dfa_with_far_state(n, 2),
    )
}

// A nonempty automaton and one that accepts nothing: the intersection is empty and the
// search visits every reachable state of the product.
fn with_empty(n: usize) -> (DFA, DFA) {
    (common::dfa(n, 2), common::empty_dfa(n, 2))
}

// ---- minimization ------------------------------------------------------------------------------

// Nothing to merge: the counter is minimal.
#[library_benchmark]
#[benches::minimal(args = [1_000, 4_000], setup = counter)]
#[benches::redundant(args = [1_000, 4_000], setup = redundant)]
#[benches::scrambled(args = [1_000, 4_000], setup = scrambled)]
fn minimize(dfa: DFA) -> usize {
    black_box(dfa.minimize().size())
}

// A Moore machine whose edges carry colors that are irrelevant for the result (#14).
fn moore_with_edge_colors(n: usize) -> MooreMachine<CharAlphabet, bool, u32> {
    let ts = common::scrambled(n, 2)
        .map_edge_colors(|_| 7u32)
        .collect_dts();
    MooreMachine::from_parts(ts, 0)
}

#[library_benchmark]
#[benches::scrambled(args = [1_000, 4_000], setup = moore_with_edge_colors)]
fn minimize_moore_with_edge_colors(mm: MooreMachine<CharAlphabet, bool, u32>) -> usize {
    black_box(mm.minimize().size())
}

// ---- boolean operations ------------------------------------------------------------------------

#[library_benchmark]
#[benches::scrambled(args = [100, 200], setup = two_scrambled)]
fn union((a, b): (DFA, DFA)) -> usize {
    black_box(a.union(&b).size())
}

#[library_benchmark]
#[benches::scrambled(args = [100, 200], setup = two_scrambled)]
fn intersection((a, b): (DFA, DFA)) -> usize {
    black_box(a.intersection(&b).size())
}

#[library_benchmark]
#[benches::empty(args = [100, 200], setup = with_empty)]
fn intersection_is_empty((a, b): (DFA, DFA)) -> bool {
    black_box(a.intersection_is_empty(&b))
}

#[library_benchmark]
#[benches::scrambled(args = [1_000, 4_000], setup = scrambled)]
fn complement(dfa: DFA) -> usize {
    black_box(dfa.map_state_colors(|c| !c).collect_dfa().size())
}

// ---- emptiness and equivalence -----------------------------------------------------------------

fn empty(n: usize) -> DFA {
    common::empty_dfa(n, 2)
}
fn far(n: usize) -> DFA {
    common::far_dfa(n, 2)
}

// Finding a word in an automaton that accepts nothing visits all reachable states.
#[library_benchmark]
#[benches::empty(args = [1_000, 4_000], setup = empty)]
#[benches::far(args = [1_000, 4_000], setup = far)]
fn give_word(dfa: DFA) -> bool {
    black_box(dfa.give_word().is_some())
}

#[library_benchmark]
#[benches::empty(args = [1_000, 4_000], setup = empty)]
fn is_empty_language(dfa: DFA) -> bool {
    black_box(dfa.is_empty_language())
}

#[library_benchmark]
#[benches::minimized(args = [100, 400], setup = with_minimized)]
#[benches::deep_difference(args = [100, 400], setup = deep_difference)]
#[benches::different(args = [100, 400], setup = two_scrambled)]
fn equivalent((a, b): (DFA, DFA)) -> bool {
    black_box(a.equivalent(&b))
}

// ---- running words -----------------------------------------------------------------------------

fn dfa_and_words(n: usize) -> (DFA, Vec<Vec<char>>) {
    let words = (0..200)
        .map(|i| common::thue_morse(20 + i % 80, 2).chars().collect())
        .collect();
    (common::dfa(n, 2), words)
}

#[library_benchmark]
#[benches::scrambled(args = [1_000], setup = dfa_and_words)]
fn accepts_many_words((dfa, words): (DFA, Vec<Vec<char>>)) -> usize {
    black_box(words.iter().filter(|w| dfa.accepts(w.as_slice())).count())
}

library_benchmark_group!(
    name = dfa;
    benchmarks = minimize, minimize_moore_with_edge_colors, union, intersection,
        intersection_is_empty, complement, give_word, is_empty_language, equivalent,
        accepts_many_words
);

main!(library_benchmark_groups = dfa);
