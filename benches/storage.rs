//! The same operations on the storages for deterministic systems over a [`CharAlphabet`]:
//! `Det<LinkedTs>` (`DTS`, benchmarks ending in `_linked`), `DenseTs` (`_dense`) and the read-only
//! `CsrTs` (`_csr`, only for the operations that do not change the system). Every operation is
//! written once, generic over the storage, and instantiated for each, so the numbers of a group
//! always measure the same work on the same input.

mod common;

use automata::alphabet::{Alphabet, CharAlphabet};
use automata::automaton::DFA;
use automata::ts::operations::{MatchingProduct, ProductIndex};
use automata::ts::{
    CsrTs, DenseTs, Deterministic, ForAlphabet, PredecessorIterable, Shrinkable, Sproutable,
};
use automata::{DTS, States, TransitionSystem, Void};
use gungraun::{Dhat, prelude::*};
use std::hint::black_box;

type Linked = DTS<CharAlphabet, bool, Void>;
type Dense = DenseTs<CharAlphabet, bool, Void>;
type Csr = CsrTs<CharAlphabet, bool, Void>;

/// What the operations that only read need from a storage.
trait ReadOnly:
    TransitionSystem<Alphabet = CharAlphabet, StateColor = bool, EdgeColor = Void, StateIndex = u32>
    + Deterministic
    + PredecessorIterable
    + States
    + Clone
{
}
impl<T> ReadOnly for T where
    T: TransitionSystem<
            Alphabet = CharAlphabet,
            StateColor = bool,
            EdgeColor = Void,
            StateIndex = u32,
        > + Deterministic
        + PredecessorIterable
        + States
        + Clone
{
}

/// What the operations that change the system need from a storage.
trait Storage: ReadOnly + Sproutable + ForAlphabet<CharAlphabet> + Shrinkable {}
impl<T> Storage for T where T: ReadOnly + Sproutable + ForAlphabet<CharAlphabet> + Shrinkable {}

// ---- inputs ------------------------------------------------------------------------------------
//
// Every input is made from the same `common` generator and converted, so both storages get the
// same transition system. Nothing here is measured.

fn convert<T: Storage>(ts: &Linked) -> T {
    T::sprout_from_ts(ts)
}

fn scrambled_linked(n: usize, k: usize) -> Linked {
    common::scrambled(n, k)
}
fn scrambled_dense(n: usize, k: usize) -> Dense {
    convert(&common::scrambled(n, k))
}
fn scrambled_csr(n: usize, k: usize) -> Csr {
    Csr::from_ts(&common::scrambled(n, k))
}

type EdgeList = (usize, usize, Vec<(u32, char, u32)>);

/// All edges of `scrambled(n, k)`, in the order of the states.
fn edge_list(n: usize, k: usize) -> EdgeList {
    let ts = common::scrambled(n, k);
    let edges = ts
        .states()
        .flat_map(|q| {
            let ts = &ts;
            common::symbols(k)
                .into_iter()
                .filter_map(move |c| ts.successor(q, c).map(|p| (q, c, p)))
        })
        .collect();
    (n, k, edges)
}

fn build<T: Storage>((n, k, edges): &EdgeList) -> T {
    let mut ts = T::for_alphabet(CharAlphabet::of_size(*k));
    for q in 0..*n {
        ts.add_state(q % 3 == 0);
    }
    for &edge in edges {
        ts.add_edge(edge);
    }
    ts
}

/// `scrambled(n, 2)` without every third edge, so that completion has something to fill.
fn partial<T: Storage>(ts: &mut T) {
    let ids: Vec<_> = ts
        .states()
        .flat_map(|q| ts.edges_from(q).unwrap().filter_map(|e| e.id()))
        .enumerate()
        .filter(|(i, _)| i % 3 == 0)
        .map(|(_, id)| id)
        .collect();
    for id in ids {
        ts.remove_edge(id);
    }
}
fn partial_linked(n: usize) -> Linked {
    let mut ts = common::scrambled(n, 2);
    partial(&mut ts);
    ts
}
fn partial_dense(n: usize) -> Dense {
    let mut ts = scrambled_dense(n, 2);
    partial(&mut ts);
    ts
}

fn word(len: usize) -> Vec<char> {
    common::word(len, 2).chars().collect()
}
fn with_word_linked(n: usize) -> (Linked, Vec<char>) {
    (common::scrambled(n, 2), word(100_000))
}
fn with_word_csr(n: usize) -> (Csr, Vec<char>) {
    (scrambled_csr(n, 2), word(100_000))
}
fn with_word_dense(n: usize) -> (Dense, Vec<char>) {
    (scrambled_dense(n, 2), word(100_000))
}

/// 1000 words of length 20, taken from consecutive windows of one long word.
fn short_words(count: usize) -> Vec<Vec<char>> {
    let long = word(count + 20);
    (0..count).map(|i| long[i..i + 20].to_vec()).collect()
}
fn with_words_linked(n: usize) -> (Linked, Vec<Vec<char>>) {
    (common::scrambled(n, 2), short_words(1_000))
}
fn with_words_csr(n: usize) -> (Csr, Vec<Vec<char>>) {
    (scrambled_csr(n, 2), short_words(1_000))
}
fn with_words_dense(n: usize) -> (Dense, Vec<Vec<char>>) {
    (scrambled_dense(n, 2), short_words(1_000))
}

type Queries = Vec<(ProductIndex<u32, u32>, char)>;
fn product_queries(n: usize) -> Queries {
    (0..1_000)
        .map(|i| {
            (
                ProductIndex(((i * 37) % n) as u32, ((i * 101 + 5) % n) as u32),
                ['a', 'b'][i % 2],
            )
        })
        .collect()
}
fn product_linked(n: usize) -> (Linked, Linked, Queries) {
    (
        common::scrambled(n, 2),
        common::counter(n, 2),
        product_queries(n),
    )
}
fn product_dense(n: usize) -> (Dense, Dense, Queries) {
    (
        scrambled_dense(n, 2),
        convert(&common::counter(n, 2)),
        product_queries(n),
    )
}

fn product_csr(n: usize) -> (Csr, Csr, Queries) {
    (
        scrambled_csr(n, 2),
        Csr::from_ts(&common::counter(n, 2)),
        product_queries(n),
    )
}

fn redundant_csr(n: usize) -> Csr {
    Csr::from_ts(&common::redundant_counter(n, 2))
}
fn redundant_linked(n: usize) -> Linked {
    common::redundant_counter(n, 2)
}
fn redundant_dense(n: usize) -> Dense {
    convert(&common::redundant_counter(n, 2))
}

// ---- the operations ----------------------------------------------------------------------------

fn add_all<T: Storage>(input: EdgeList) -> T {
    build(&input)
}

/// Builds the system, then replaces the target of every edge, which a dense table overwrites in
/// place and a linked list replaces by removing and adding.
fn overwrite_all<T: Storage>(input: EdgeList) -> T {
    let mut ts: T = build(&input);
    let n = input.0 as u32;
    for &(q, c, p) in &input.2 {
        ts.add_edge((q, c, (p + 1) % n));
    }
    ts
}

fn successors<T: ReadOnly>(ts: &T, k: usize) -> u64 {
    let symbols = common::symbols(k);
    let mut sum = 0u64;
    for q in ts.states() {
        for &c in &symbols {
            sum += ts.successor(q, c).unwrap_or(0) as u64;
        }
    }
    black_box(sum)
}

fn edges_from<T: ReadOnly>(ts: &T) -> usize {
    black_box(
        ts.states()
            .map(|q| ts.edges_from(q).map_or(0, |e| e.count()))
            .sum(),
    )
}

fn predecessors<T: ReadOnly>(ts: &T) -> usize {
    black_box(
        ts.states()
            .map(|q| ts.predecessors(q).map_or(0, |p| p.count()))
            .sum(),
    )
}

fn reachable<T: ReadOnly>(ts: &T) -> usize {
    black_box(ts.reachable_state_indices_from(0).count())
}

fn run_one_word<T: ReadOnly>((ts, word): &(T, Vec<char>)) -> u64 {
    black_box(ts.reached_state_from(0, word.as_slice()).unwrap_or(0) as u64)
}

fn run_many_words<T: ReadOnly>((ts, words): &(T, Vec<Vec<char>>)) -> u64 {
    black_box(
        words
            .iter()
            .map(|w| ts.reached_state_from(0, w.as_slice()).unwrap_or(0) as u64)
            .sum(),
    )
}

fn product_successors<T: ReadOnly>((l, r, queries): &(T, T, Queries)) -> usize {
    let product = MatchingProduct(&l, &r);
    black_box(
        queries
            .iter()
            .filter(|&&(q, c)| product.successor(q, c).is_some())
            .count(),
    )
}

fn minimize<T: ReadOnly>(ts: &T) -> usize {
    black_box(DFA::from_parts(ts, 0).minimize().state_count())
}

fn complete<T: Storage>(mut ts: T) -> T {
    ts.complete_with_colors(false, Void);
    ts
}

fn remove_states<T: Storage>(mut ts: T) -> T {
    let n = ts.state_count();
    for i in 0..1_000 {
        black_box(ts.remove_state((i * (n / 1_000)) as u32));
    }
    ts
}

fn clone_ts<T: Clone>(ts: T) -> (T, T) {
    let copy = black_box(ts.clone());
    (ts, copy)
}

// ---- benchmarks, each operation once per storage ---------------------------------------------

#[library_benchmark]
#[bench::k2_5000(args = (5_000, 2), setup = edge_list)]
#[bench::k8_5000(args = (5_000, 8), setup = edge_list)]
fn add_edges_linked(input: EdgeList) -> Linked {
    add_all(input)
}
#[library_benchmark]
#[bench::k2_5000(args = (5_000, 2), setup = edge_list)]
#[bench::k8_5000(args = (5_000, 8), setup = edge_list)]
fn add_edges_dense(input: EdgeList) -> Dense {
    add_all(input)
}

#[library_benchmark]
#[bench::k2_5000(args = (5_000, 2), setup = edge_list)]
fn overwrite_edges_linked(input: EdgeList) -> Linked {
    overwrite_all(input)
}
#[library_benchmark]
#[bench::k2_5000(args = (5_000, 2), setup = edge_list)]
fn overwrite_edges_dense(input: EdgeList) -> Dense {
    overwrite_all(input)
}

#[library_benchmark]
#[bench::k2_2000(args = (2_000, 2), setup = scrambled_linked)]
#[bench::k8_2000(args = (2_000, 8), setup = scrambled_linked)]
fn successor_all_pairs_linked(ts: Linked) -> (Linked, u64) {
    let k = ts.alphabet().size();
    let sum = successors(&ts, k);
    (ts, sum)
}
#[library_benchmark]
#[bench::k2_2000(args = (2_000, 2), setup = scrambled_dense)]
#[bench::k8_2000(args = (2_000, 8), setup = scrambled_dense)]
fn successor_all_pairs_dense(ts: Dense) -> (Dense, u64) {
    let k = ts.alphabet().size();
    let sum = successors(&ts, k);
    (ts, sum)
}

#[library_benchmark]
#[bench::k2_2000(args = (2_000, 2), setup = scrambled_linked)]
#[bench::k8_2000(args = (2_000, 8), setup = scrambled_linked)]
fn edges_from_all_states_linked(ts: Linked) -> (Linked, usize) {
    let result = edges_from(&ts);
    (ts, result)
}
#[library_benchmark]
#[bench::k2_2000(args = (2_000, 2), setup = scrambled_dense)]
#[bench::k8_2000(args = (2_000, 8), setup = scrambled_dense)]
fn edges_from_all_states_dense(ts: Dense) -> (Dense, usize) {
    let result = edges_from(&ts);
    (ts, result)
}

#[library_benchmark]
#[bench::k2_2000(args = (2_000, 2), setup = scrambled_linked)]
fn predecessors_of_all_states_linked(ts: Linked) -> (Linked, usize) {
    let result = predecessors(&ts);
    (ts, result)
}
#[library_benchmark]
#[bench::k2_2000(args = (2_000, 2), setup = scrambled_dense)]
fn predecessors_of_all_states_dense(ts: Dense) -> (Dense, usize) {
    let result = predecessors(&ts);
    (ts, result)
}

#[library_benchmark]
#[bench::k2_8000(args = (8_000, 2), setup = scrambled_linked)]
fn reachable_states_linked(ts: Linked) -> (Linked, usize) {
    let result = reachable(&ts);
    (ts, result)
}
#[library_benchmark]
#[bench::k2_8000(args = (8_000, 2), setup = scrambled_dense)]
fn reachable_states_dense(ts: Dense) -> (Dense, usize) {
    let result = reachable(&ts);
    (ts, result)
}

#[library_benchmark]
#[bench::len_100000(args = (1_000), setup = with_word_linked)]
fn run_one_word_linked(input: (Linked, Vec<char>)) -> ((Linked, Vec<char>), u64) {
    let result = run_one_word(&input);
    (input, result)
}
#[library_benchmark]
#[bench::len_100000(args = (1_000), setup = with_word_dense)]
fn run_one_word_dense(input: (Dense, Vec<char>)) -> ((Dense, Vec<char>), u64) {
    let result = run_one_word(&input);
    (input, result)
}

#[library_benchmark]
#[bench::count_1000(args = (1_000), setup = with_words_linked)]
fn run_many_words_linked(input: (Linked, Vec<Vec<char>>)) -> ((Linked, Vec<Vec<char>>), u64) {
    let result = run_many_words(&input);
    (input, result)
}
#[library_benchmark]
#[bench::count_1000(args = (1_000), setup = with_words_dense)]
fn run_many_words_dense(input: (Dense, Vec<Vec<char>>)) -> ((Dense, Vec<Vec<char>>), u64) {
    let result = run_many_words(&input);
    (input, result)
}

#[library_benchmark]
#[bench::n200(args = (200), setup = product_linked)]
fn product_successor_linked(
    input: (Linked, Linked, Queries),
) -> ((Linked, Linked, Queries), usize) {
    let result = product_successors(&input);
    (input, result)
}
#[library_benchmark]
#[bench::n200(args = (200), setup = product_dense)]
fn product_successor_dense(input: (Dense, Dense, Queries)) -> ((Dense, Dense, Queries), usize) {
    let result = product_successors(&input);
    (input, result)
}

#[library_benchmark]
#[bench::redundant_2000(args = (2_000), setup = redundant_linked)]
#[bench::redundant_8000(args = (8_000), setup = redundant_linked)]
fn minimize_linked(ts: Linked) -> (Linked, usize) {
    let result = minimize(&ts);
    (ts, result)
}
#[library_benchmark]
#[bench::redundant_2000(args = (2_000), setup = redundant_dense)]
#[bench::redundant_8000(args = (8_000), setup = redundant_dense)]
fn minimize_dense(ts: Dense) -> (Dense, usize) {
    let result = minimize(&ts);
    (ts, result)
}

#[library_benchmark]
#[bench::partial_5000(args = (5_000), setup = partial_linked)]
fn complete_linked(ts: Linked) -> Linked {
    complete(ts)
}
#[library_benchmark]
#[bench::partial_5000(args = (5_000), setup = partial_dense)]
fn complete_dense(ts: Dense) -> Dense {
    complete(ts)
}

#[library_benchmark]
#[bench::k2_10000(args = (10_000, 2), setup = scrambled_linked)]
fn remove_state_linked(ts: Linked) -> Linked {
    remove_states(ts)
}
#[library_benchmark]
#[bench::k2_10000(args = (10_000, 2), setup = scrambled_dense)]
fn remove_state_dense(ts: Dense) -> Dense {
    remove_states(ts)
}

#[library_benchmark]
#[bench::k2_10000(args = (10_000, 2), setup = scrambled_linked)]
fn clone_linked(ts: Linked) -> (Linked, Linked) {
    clone_ts(ts)
}
#[library_benchmark]
#[bench::k2_10000(args = (10_000, 2), setup = scrambled_dense)]
fn clone_dense(ts: Dense) -> (Dense, Dense) {
    clone_ts(ts)
}

#[library_benchmark]
#[bench::k2_2000(args = (2_000, 2), setup = scrambled_csr)]
#[bench::k8_2000(args = (2_000, 8), setup = scrambled_csr)]
fn successor_all_pairs_csr(ts: Csr) -> (Csr, u64) {
    let k = ts.alphabet().size();
    let sum = successors(&ts, k);
    (ts, sum)
}

#[library_benchmark]
#[bench::k2_2000(args = (2_000, 2), setup = scrambled_csr)]
#[bench::k8_2000(args = (2_000, 8), setup = scrambled_csr)]
fn edges_from_all_states_csr(ts: Csr) -> (Csr, usize) {
    let result = edges_from(&ts);
    (ts, result)
}

#[library_benchmark]
#[bench::k2_2000(args = (2_000, 2), setup = scrambled_csr)]
fn predecessors_of_all_states_csr(ts: Csr) -> (Csr, usize) {
    let result = predecessors(&ts);
    (ts, result)
}

#[library_benchmark]
#[bench::k2_8000(args = (8_000, 2), setup = scrambled_csr)]
fn reachable_states_csr(ts: Csr) -> (Csr, usize) {
    let result = reachable(&ts);
    (ts, result)
}

#[library_benchmark]
#[bench::len_100000(args = (1_000), setup = with_word_csr)]
fn run_one_word_csr(input: (Csr, Vec<char>)) -> ((Csr, Vec<char>), u64) {
    let result = run_one_word(&input);
    (input, result)
}

#[library_benchmark]
#[bench::count_1000(args = (1_000), setup = with_words_csr)]
fn run_many_words_csr(input: (Csr, Vec<Vec<char>>)) -> ((Csr, Vec<Vec<char>>), u64) {
    let result = run_many_words(&input);
    (input, result)
}

#[library_benchmark]
#[bench::n200(args = (200), setup = product_csr)]
fn product_successor_csr(input: (Csr, Csr, Queries)) -> ((Csr, Csr, Queries), usize) {
    let result = product_successors(&input);
    (input, result)
}

#[library_benchmark]
#[bench::redundant_2000(args = (2_000), setup = redundant_csr)]
#[bench::redundant_8000(args = (8_000), setup = redundant_csr)]
fn minimize_csr(ts: Csr) -> (Csr, usize) {
    let result = minimize(&ts);
    (ts, result)
}

#[library_benchmark]
#[bench::k2_10000(args = (10_000, 2), setup = scrambled_csr)]
fn clone_csr(ts: Csr) -> (Csr, Csr) {
    clone_ts(ts)
}

library_benchmark_group!(
    name = storage;
    benchmarks =
        add_edges_linked, add_edges_dense,
        overwrite_edges_linked, overwrite_edges_dense,
        successor_all_pairs_linked, successor_all_pairs_dense,
        edges_from_all_states_linked, edges_from_all_states_dense,
        predecessors_of_all_states_linked, predecessors_of_all_states_dense,
        reachable_states_linked, reachable_states_dense,
        run_one_word_linked, run_one_word_dense,
        run_many_words_linked, run_many_words_dense,
        product_successor_linked, product_successor_dense,
        minimize_linked, minimize_dense,
        complete_linked, complete_dense,
        remove_state_linked, remove_state_dense,
        clone_linked, clone_dense,
        successor_all_pairs_csr, edges_from_all_states_csr, predecessors_of_all_states_csr,
        reachable_states_csr, run_one_word_csr, run_many_words_csr, product_successor_csr,
        minimize_csr, clone_csr
);

main!(
    config = LibraryBenchmarkConfig::default().tool(Dhat::default()),
    library_benchmark_groups = storage
);
