//! Printing an automaton in the DOT format.
//!
//! Run with `cargo run --example dot`, the output can be rendered with graphviz, for example
//! `cargo run --example dot | dot -Tsvg > automaton.svg`.

use automata::{dot::Dottable, ts::Builder};

fn main() {
    let dfa = Builder::without_edge_colors()
        .with_state_colors([true, false])
        .with_transitions([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (1, 'b', 1)])
        .into_dfa(0);

    println!("{}", dfa.dot_representation());
}
