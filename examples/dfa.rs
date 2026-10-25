//! Building DFAs, combining them with boolean operations and minimizing them.
//!
//! Run with `cargo run --example dfa`.

use automata::{TransitionSystem, automaton::DFA, ts::Builder};

/// The DFA over `{a, b}` that accepts the words in which the number of `a`s leaves the given
/// remainder when divided by three.
fn a_count_mod_three(remainder: usize) -> DFA {
    Builder::without_edge_colors()
        // only the state that corresponds to the remainder is accepting
        .with_state_colors((0..3).map(|state| state == remainder))
        .with_transitions([
            (0, 'a', 1),
            (0, 'b', 0),
            (1, 'a', 2),
            (1, 'b', 1),
            (2, 'a', 0),
            (2, 'b', 2),
        ])
        .into_dfa(0)
}

fn main() {
    let zero = a_count_mod_three(0);
    let one = a_count_mod_three(1);

    println!("word      0 mod 3   1 mod 3   union");
    let union = zero.union(&one);
    for word in ["", "a", "aa", "aaa", "abab", "baaab"] {
        println!(
            "{word:<8}  {:<8}  {:<8}  {}",
            zero.accepts(word),
            one.accepts(word),
            union.accepts(word)
        );
    }

    // the operations are lazy, but every result is an automaton again
    assert!(zero.intersection(&one).is_empty_language());
    assert!(!zero.equivalent(&one));
    assert!(zero.negation().accepts("a"));

    // a DFA with redundant states: it accepts the words that end with an `a`, but state 3
    // behaves exactly like state 1
    let redundant = Builder::without_edge_colors()
        .with_state_colors([false, true, false, true])
        .with_transitions([
            (0, 'a', 1),
            (0, 'b', 2),
            (1, 'a', 3),
            (1, 'b', 2),
            (2, 'a', 1),
            (2, 'b', 0),
            (3, 'a', 1),
            (3, 'b', 2),
        ])
        .into_dfa(0);
    let minimized = redundant.clone().minimize();
    println!(
        "minimization: {} states -> {} states",
        redundant.size(),
        minimized.size()
    );
    assert!(redundant.equivalent(&minimized));
    assert_eq!(minimized.size(), 2);
}
