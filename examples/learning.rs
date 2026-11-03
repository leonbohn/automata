//! Learning automata: passively from a sample (sprout) and actively with L* against an oracle.
//!
//! Run with `cargo run --example learning --features learning`.

use automata::alphabet::CharAlphabet;
use automata::automaton::{BuchiCondition, MealyMachine};
use automata::learning::active::{LStar, MealyOracle};
use automata::learning::passive::{OmegaSample, sprout::sprout};
use automata::ts::Builder;
use automata::{States, TransitionSystem, upw};

fn main() {
    // Passive learning: a deterministic Büchi automaton that is consistent with a sample of
    // ultimately periodic words, here the words with infinitely many `a`.
    let sample = OmegaSample::new_omega_from_pos_neg(
        CharAlphabet::of_size(2),
        [upw!("a"), upw!("a", "b"), upw!("bbb", "ab")],
        [upw!("b"), upw!("aa", "b")],
    );
    let dba = sprout(sample.clone(), BuchiCondition).expect("the sample is consistent");
    for word in sample.positive_words() {
        assert!(dba.accepts(word));
    }
    for word in sample.negative_words() {
        assert!(!dba.accepts(word));
    }
    println!("sprout found a DBA with {} states", dba.state_count());

    // Active learning: L* learns a Mealy machine by asking an oracle, which is here the target
    // machine itself.
    let target = Builder::without_state_colors()
        .with_edges([
            (0, 'a', 0, 0),
            (0, 'b', 1, 1),
            (0, 'c', 2, 2),
            (1, 'a', 0, 2),
            (1, 'b', 1, 1),
            (1, 'c', 2, 2),
            (2, 'a', 2, 2),
            (2, 'b', 0, 0),
            (2, 'c', 1, 2),
        ])
        .into_mealy(0);
    let alphabet = target.alphabet().clone();
    let oracle = MealyOracle::new(target).expect("the target is complete");
    let learned: MealyMachine = LStar::new(alphabet, oracle)
        .infer()
        .expect("L* terminates for a Mealy machine");
    println!(
        "L* learned a Mealy machine with {} states",
        learned.state_count()
    );
}
