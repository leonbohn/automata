//! Deterministic parity automata over infinite words.
//!
//! Run with `cargo run --example parity`.

use automata::{ts::Builder, upw};

fn main() {
    // The edges are labeled with priorities, the automaton accepts a word if the smallest
    // priority that is seen infinitely often is even.
    let dpa = Builder::without_state_colors()
        // (source, symbol, priority, target)
        .with_transitions([
            (0, 'a', 1, 1),
            (0, 'b', 0, 0),
            (1, 'a', 1, 0),
            (1, 'b', 2, 1),
        ])
        .into_dpa(0);

    // Infinite words are written as `u v^ω` with the macro `upw!(u, v)`, or just `upw!(v)`.
    let words = [
        ("b^ω", upw!("b")),
        ("a^ω", upw!("a")),
        ("(ab)^ω", upw!("ab")),
        ("bb a^ω", upw!("bb", "a")),
    ];
    for (name, word) in &words {
        println!("{name:<8} accepted: {}", dpa.accepts(word));
    }

    // Complementing a deterministic parity automaton is cheap, and so is comparing languages.
    let complement = dpa.clone().complement();
    for (_, word) in &words {
        assert_ne!(dpa.accepts(word), complement.accepts(word));
    }
    assert!(dpa.language_equivalent(&complement.clone().complement()));
    assert!(!dpa.language_equivalent(&complement));

    // If the language is not empty, we can ask for a word that is accepted.
    let witness = dpa.give_accepted_word().expect("the language is not empty");
    println!("an accepted word: {witness:?}");
    assert!(dpa.accepts(&witness));
}
