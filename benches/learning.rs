//! The learning algorithms: sprout (passive) and L* (active).

mod common;

use automata::alphabet::CharAlphabet;
use automata::automaton::{MealyMachine, MinEvenParityCondition};
use automata::learning::active::{LStar, MealyOracle};
use automata::learning::passive::{OmegaSample, sprout::sprout};
use automata::representation::CollectPointed;
use automata::ts::Builder;
use automata::word::{OmegaWord, ReducedOmegaWord};
use automata::{DTS, Int, States, TransitionSystem, Void};
use gungraun::{Dhat, prelude::*};
use std::hint::black_box;

// A sample of `count` lassos, classified by the language "infinitely many `a`s and `b`s". A consistent
// automaton exists, but sprout has to find it.
fn parity_sample(count: usize) -> OmegaSample {
    let mut sample = OmegaSample::new_for_alphabet(CharAlphabet::of_size(2));
    for i in 0..count {
        // binary expansions of i and 7 i + 3 as spoke and cycle
        let bits = |n: usize, len: usize| -> String {
            (0..len)
                .map(|k| if (n >> k) & 1 == 0 { 'a' } else { 'b' })
                .collect()
        };
        let spoke = bits(i, 3 + i % 5);
        let cycle = bits(7 * i + 3, 1 + i % 4);
        let word = ReducedOmegaWord::try_from_str(&format!("{spoke},{cycle}")).unwrap();
        let cycle = word.cycle_vec();
        let accepted = cycle.contains(&'a') && cycle.contains(&'b');
        if !sample.contains(&word) {
            sample.insert(word, accepted).unwrap();
        }
    }
    sample
}

// ---- passive learning --------------------------------------------------------------------------

// The result is irrelevant, the algorithm falls back to the default automaton if it exceeds its
// threshold.
#[library_benchmark]
#[bench::inf_ab_100(args = (100), setup = parity_sample)]
#[bench::inf_ab_400(args = (400), setup = parity_sample)]
fn sprout_parity(sample: OmegaSample) -> usize {
    match sprout(sample, MinEvenParityCondition) {
        Ok(dpa) => black_box(dpa.state_count()),
        Err(error) => black_box(format!("{error:?}").len()),
    }
}

// ---- active learning ---------------------------------------------------------------------------

// A Mealy machine with `n` states that is minimal: it counts the `a`s modulo `n` and outputs the
// state that it reaches (on `b` the output is the current state).
fn mealy_target(n: usize) -> MealyMachine<DTS<CharAlphabet, Void, Int>> {
    Builder::without_state_colors()
        .with_edges((0..n as u32).flat_map(|q| {
            let next = (q + 1) % n as u32;
            [(q, 'a', next as Int, next), (q, 'b', q as Int, q)]
        }))
        .into_dts_with_initial(0)
        .collect_mealy()
}

#[library_benchmark]
#[bench::counting_8(args = (8), setup = mealy_target)]
#[bench::counting_16(args = (16), setup = mealy_target)]
fn lstar_mealy(target: MealyMachine<DTS<CharAlphabet, Void, Int>>) -> usize {
    let alphabet = target.alphabet().clone();
    let oracle = MealyOracle::new(target).unwrap();
    let learned: MealyMachine = LStar::new(alphabet, oracle).infer().unwrap();
    black_box(learned.state_count())
}

library_benchmark_group!(
    name = learning;
    benchmarks = sprout_parity, lstar_mealy
);

main!(
    config = LibraryBenchmarkConfig::default().tool(Dhat::default()),
    library_benchmark_groups = learning
);
