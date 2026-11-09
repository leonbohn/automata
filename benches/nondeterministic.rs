//! Nondeterministic omega automata (`Existential` semantics): acceptance of lassos, which searches
//! the product with the cycle of the word, and emptiness with a witness.

mod common;

use automata::alphabet::CharAlphabet;
use automata::alphabet::PropAlphabet;
use automata::automaton::{
    Automaton, BuchiCondition, CoBuchiCondition, Emptiness, Existential, MinEvenParityCondition,
    MullerCondition, NBA, NCA, NMA, NPA, NRA, NondeterministicOmegaAutomaton, RabinCondition,
    RabinPair,
};
use automata::word::ReducedOmegaWord;
use automata::{Int, NTS, TransitionSystem, Void};
use common::at;
use gungraun::prelude::*;
use std::hint::black_box;

type Npa = NPA<NTS<CharAlphabet, Void, Int>>;

/// Priorities `0..4`: the whole system sees priority 0, so a good cycle exists.
fn npa(n: usize) -> Npa {
    let ts = common::scrambled_omega_nts(n, |x| (x % 4) as Int);
    Automaton::from_parts_with_acceptance(ts, at(0), Existential(MinEvenParityCondition))
}

/// Only odd priorities: the language is empty, and each priority is removed in turn.
fn empty_npa(n: usize) -> Npa {
    let ts = common::scrambled_omega_nts(n, |x| (2 * (x % 4) + 1) as Int);
    Automaton::from_parts_with_acceptance(ts, at(0), Existential(MinEvenParityCondition))
}

fn nba(n: usize) -> NBA {
    let ts = common::scrambled_omega_nts(n, |x| x % 5 == 0);
    Automaton::from_parts_with_acceptance(ts, at(0), Existential(BuchiCondition))
}

fn nca(n: usize) -> NCA {
    let ts = common::scrambled_omega_nts(n, |x| x % 5 == 0);
    Automaton::from_parts_with_acceptance(ts, at(0), Existential(CoBuchiCondition))
}

/// Min-even parity on `1..=4` as Rabin pairs, so the least priority 1 has to be avoided first.
fn nra(n: usize) -> NRA<NTS<CharAlphabet, Void, Int>> {
    let ts = common::scrambled_omega_nts(n, |x| (x % 4 + 1) as Int);
    let pairs: RabinCondition<Int> = [
        RabinPair::from_iters([1], [2]),
        RabinPair::from_iters([1, 2, 3], [4]),
    ]
    .into();
    Automaton::from_parts_with_acceptance(ts, at(0), Existential(pairs))
}

/// Accepting exactly if `{1, 2}` is seen infinitely often: the default decomposition has to
/// leave out colors one by one.
fn nma(n: usize) -> NMA<NTS<CharAlphabet, Void, Int>> {
    let ts = common::scrambled_omega_nts(n, |x| (x % 4) as Int);
    let condition = MullerCondition::from_iter_iter([[1, 2]]);
    Automaton::from_parts_with_acceptance(ts, at(0), Existential(condition))
}

fn lassos() -> Vec<ReducedOmegaWord<char>> {
    common::lassos(10, 2, 10, 20)
        .into_iter()
        .map(|(u, v)| ReducedOmegaWord::ultimately_periodic(u.as_str(), v.as_str()))
        .collect()
}

fn with_lassos<A>(automaton: A) -> (A, Vec<ReducedOmegaWord<char>>) {
    (automaton, lassos())
}

// ---- acceptance of lassos ----------------------------------------------------------------------

#[library_benchmark]
#[bench::npa_100(args = (npa(100)), setup = with_lassos)]
#[bench::npa_400(args = (npa(400)), setup = with_lassos)]
#[bench::empty_npa_400(args = (empty_npa(400)), setup = with_lassos)]
fn npa_accepts((npa, words): (Npa, Vec<ReducedOmegaWord<char>>)) -> usize {
    black_box(words.iter().filter(|w| npa.accepts(*w)).count())
}

#[library_benchmark]
#[bench::nba_400(args = (nba(400)), setup = with_lassos)]
fn nba_accepts((nba, words): (NBA, Vec<ReducedOmegaWord<char>>)) -> usize {
    black_box(words.iter().filter(|w| nba.accepts(*w)).count())
}

#[library_benchmark]
#[bench::nca_400(args = (nca(400)), setup = with_lassos)]
fn nca_accepts((nca, words): (NCA, Vec<ReducedOmegaWord<char>>)) -> usize {
    black_box(words.iter().filter(|w| nca.accepts(*w)).count())
}

type NondeterministicFixture = NondeterministicOmegaAutomaton<PropAlphabet>;

fn ltl_nondeterministic() -> Vec<NondeterministicFixture> {
    common::fixture_texts(common::LTL)
        .iter()
        .map(|text| common::parse_nondeterministic(text))
        .collect()
}

// The deterministic fixtures read with the nondeterministic storage: the existential semantics on
// automata whose acceptance has a deterministic counterpart in `runs`.
#[library_benchmark]
#[bench::ltl(setup = ltl_nondeterministic)]
fn fixture_accepts(automata: Vec<NondeterministicFixture>) -> usize {
    let mut accepted = 0;
    for aut in &automata {
        let word = common::fixture_lasso(aut.ts().alphabet(), 5, 7);
        accepted += usize::from(aut.accepts(&word));
    }
    black_box(accepted)
}

// ---- emptiness ---------------------------------------------------------------------------------

#[library_benchmark]
#[bench::npa_1000(args = (1_000), setup = npa)]
#[bench::npa_4000(args = (4_000), setup = npa)]
#[bench::empty_npa_1000(args = (1_000), setup = empty_npa)]
#[bench::empty_npa_4000(args = (4_000), setup = empty_npa)]
fn npa_witness(npa: Npa) -> bool {
    black_box(Emptiness::of(&npa).witness().is_some())
}

#[library_benchmark]
#[bench::nba_4000(args = (4_000), setup = nba)]
fn nba_witness(nba: NBA) -> bool {
    black_box(Emptiness::of(&nba).witness().is_some())
}

#[library_benchmark]
#[bench::nca_4000(args = (4_000), setup = nca)]
fn nca_witness(nca: NCA) -> bool {
    black_box(Emptiness::of(&nca).witness().is_some())
}

#[library_benchmark]
#[bench::nra_4000(args = (4_000), setup = nra)]
fn nra_witness(nra: NRA<NTS<CharAlphabet, Void, Int>>) -> bool {
    black_box(Emptiness::of(&nra).witness().is_some())
}

#[library_benchmark]
#[bench::nma_1000(args = (1_000), setup = nma)]
fn nma_witness(nma: NMA<NTS<CharAlphabet, Void, Int>>) -> bool {
    black_box(Emptiness::of(&nma).witness().is_some())
}

library_benchmark_group!(
    name = nondeterministic;
    benchmarks = npa_accepts, nba_accepts, nca_accepts, fixture_accepts, npa_witness,
        nba_witness, nca_witness, nra_witness, nma_witness
);

main!(library_benchmark_groups = nondeterministic);
