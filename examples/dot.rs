//! Printing an automaton in the DOT format and, with the features `render` or `graphviz`,
//! rendering it.
//!
//! Run with `cargo run --example dot`, the output can be rendered with graphviz, for example
//! `cargo run --example dot | dot -Tsvg > automaton.svg`.
//!
//! With `--all-features`, a data URL is printed that can be pasted into a browser, and
//! `cargo run --all-features --example dot -- --show` opens the rendered automaton in the
//! viewer of your system (set `IMAGE_VIEWER` to use a different program).

use automata::{dot::Dottable, ts::Builder};

fn main() {
    let dfa = Builder::without_edge_colors()
        .with_state_colors([true, false])
        .with_transitions([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (1, 'b', 1)])
        .into_dfa(0);

    println!("{}", dfa.dot_representation());

    #[cfg(feature = "render")]
    {
        let data_url = dfa.try_data_url().expect("cannot render into data URL");
        println!("Paste this into your browser:\n{data_url}");
        if std::env::args().any(|arg| arg == "--show") {
            dfa.display_rendered().expect("cannot display the image");
        }
    }

    #[cfg(feature = "graphviz")]
    if std::env::args().any(|arg| arg == "--show-graphviz") {
        dfa.display_rendered_graphviz()
            .expect("cannot display the image, is graphviz installed?");
    }
}
