//! Transition systems: reachability, strongly connected components and lazy operations.
//!
//! Run with `cargo run --example transition_system`.

use automata::States;
use automata::{
    math,
    representation::CollectTs,
    ts::{Builder, TransitionSystem},
};

fn main() {
    // States 0, 1 and 2 form a strongly connected component, state 3 is a sink.
    let dfa = Builder::without_edge_colors()
        .with_state_colors([true, false, true, false])
        .with_transitions([
            (0, 'a', 2),
            (0, 'b', 1),
            (0, 'c', 3),
            (1, 'a', 0),
            (1, 'b', 2),
            (1, 'c', 3),
            (2, 'a', 2),
            (2, 'b', 1),
            (2, 'c', 3),
            (3, 'a', 3),
            (3, 'b', 3),
            (3, 'c', 3),
        ])
        .into_dfa(0);

    let reachable: math::FxIndexSet<_> = dfa.reachable_state_indices().collect();
    println!("reachable from the initial state: {reachable:?}");
    let from_sink: math::FxIndexSet<_> = dfa.reachable_state_indices_from(3).collect();
    println!("reachable from state 3:           {from_sink:?}");

    let sccs = dfa.sccs();
    println!("{} strongly connected components:", sccs.size());
    for (index, scc) in sccs.iter() {
        println!("  {index:?}: {:?}", scc.iter().collect::<Vec<_>>());
    }
    assert_eq!(sccs.size(), 2);

    // Operations on transition systems do not copy anything, they compute on demand. Here we
    // look at the transition system without the sink.
    let without_sink = (&dfa).restrict_state_indices(|state| state < 3);
    // `collect_dts` evaluates everything and stores the result in a new transition system.
    let collected = without_sink.collect_dts();
    println!("without the sink: {} states", collected.size());
    assert_eq!(collected.size(), 3);
}
