//! Deterministic inputs shared by the benchmarks.
//!
//! Nothing in here is random: every generator is a pure function of its size parameters, and the
//! fixtures are files that are committed to the repository (see `benches/fixtures/README.md`).
//! Irregular but fixed structure comes from affine maps modulo `n` ([`scrambled`]).
#![allow(dead_code)]

use std::path::{Path, PathBuf};

use automata::alphabet::{CharAlphabet, PropAlphabet};
use automata::automaton::{DFA, DPA};
use automata::hoa::HoaString;
use automata::representation::IntoTransitions;
use automata::ts::{DenseId, ForAlphabet, Sproutable, StateId};
use automata::word::ReducedOmegaWord;
use automata::{DTS, Int, NTS, TransitionSystem, Void};

/// A DTS with boolean state colors and no edge colors, the shape a [`DFA`] is made from.
pub type Dts = DTS<CharAlphabet, bool, Void>;

/// The state with index `n`.
pub fn at(n: usize) -> StateId {
    StateId::from_usize(n)
}

/// The symbols of an alphabet of size `k`.
pub fn symbols(k: usize) -> Vec<char> {
    ('a'..).take(k).collect()
}

/// Builds the deterministic TS over `k` symbols where `successor(q, i)` is the target of the
/// `i`-th symbol from state `q` and `accepting(q)` is the color of `q`.
pub fn build(
    n: usize,
    k: usize,
    accepting: impl Fn(usize) -> bool,
    successor: impl Fn(usize, usize) -> usize,
) -> Dts {
    let mut ts = DTS::for_alphabet(CharAlphabet::of_size(k));
    for q in 0..n {
        ts.add_state(accepting(q));
    }
    for q in 0..n {
        for (i, sym) in symbols(k).into_iter().enumerate() {
            ts.add_edge((at(q), sym, at(successor(q, i))));
        }
    }
    ts
}

// ---------------------------------------------------------------------------------------------
// Graph shapes, mostly for strongly connected component decompositions
// ---------------------------------------------------------------------------------------------

/// A single cycle `0 -> 1 -> ... -> n-1 -> 0`, hence one SCC and exactly one back edge.
pub fn ring(n: usize) -> Dts {
    build(n, 2, |q| q % 2 == 0, |q, _| (q + 1) % n)
}

/// A path `0 -> 1 -> ... -> n-1 -> 0` where in addition every state has an edge back to `0`.
/// There is one SCC and `n` back edges that all target the bottom of the DFS stack.
pub fn back_edges(n: usize) -> Dts {
    build(
        n,
        2,
        |q| q % 2 == 0,
        |q, i| if i == 0 { (q + 1) % n } else { 0 },
    )
}

/// A path without any cycle (except for a self loop at the end): `n` singleton SCCs.
pub fn path(n: usize) -> Dts {
    build(n, 2, |q| q % 2 == 0, |q, _| (q + 1).min(n - 1))
}

/// Chains of 4-cycles, each of which jumps to the first state of the next one.
pub fn small_cycles(n: usize) -> Dts {
    let n = n.next_multiple_of(4);
    build(
        n,
        2,
        |q| q % 3 == 0,
        |q, i| {
            let block = q / 4;
            if i == 0 || q % 4 != 3 {
                block * 4 + (q % 4 + 1) % 4
            } else {
                ((block + 1) * 4).min(n - 4)
            }
        },
    )
}

/// A complete binary tree with `n` states in heap order whose leaves return to the root. The
/// whole system is one SCC, but depth first search goes `log n` deep before the first back edge.
pub fn binary_tree(n: usize) -> Dts {
    build(
        n,
        2,
        |q| q % 2 == 0,
        |q, i| {
            let child = 2 * q + 1 + i;
            if child < n { child } else { 0 }
        },
    )
}

/// A `width` times `n / width` grid with edges to the right and downwards, wrapping around.
pub fn grid(n: usize, width: usize) -> Dts {
    let height = n.div_ceil(width);
    let n = width * height;
    build(
        n,
        2,
        |q| (q % width + q / width).is_multiple_of(2),
        |q, i| {
            let (x, y) = (q % width, q / width);
            if i == 0 {
                y * width + (x + 1) % width
            } else {
                ((y + 1) % height) * width + x
            }
        },
    )
}

/// A DTS with irregular but completely fixed structure in which every state is reachable from
/// `0`: the first symbol goes to `q + 1 mod n` and symbol `i > 0` leads from `q` to
/// `(q * (2i + 3) + 7i + 1) mod n`.
pub fn scrambled(n: usize, k: usize) -> Dts {
    build(
        n,
        k,
        |q| q % 3 == 0,
        |q, i| {
            if i == 0 {
                (q + 1) % n
            } else {
                (q * (2 * i + 3) + 7 * i + 1) % n
            }
        },
    )
}

/// Like [`scrambled`] but without the chain on the first symbol: all symbols are affine maps
/// modulo `n`. Only part of the states is reachable and there are several SCCs of different sizes.
pub fn fragmented(n: usize, k: usize) -> Dts {
    build(
        n,
        k,
        |q| q % 3 == 0,
        |q, i| (q * (2 * i + 3) + 7 * i + 1) % n,
    )
}

/// The counter modulo `n` over `k` symbols: symbol `0` increments, symbol `i` adds `i + 1`.
/// Only state `0` is accepting. This is the minimal DFA of "the sum of the word is divisible
/// by `n`", so minimization finds nothing to merge.
pub fn counter(n: usize, k: usize) -> Dts {
    build(n, k, |q| q == 0, |q, i| (q + i + 1) % n)
}

/// A counter in which states `q` and `q + n / 2` behave identically: `n` states that minimize to
/// `n / 2`. Gives minimization something to do.
pub fn redundant_counter(n: usize, k: usize) -> Dts {
    let half = (n / 2).max(1);
    build(
        n,
        k,
        |q| q % half == 0,
        |q, i| (q + i + 1) % half + half * (q / half),
    )
}

/// An NFA over `{a, b}` accepting the words whose `n`-th symbol from the end is `a`. Its subset
/// construction has `2^n` reachable states.
pub fn nth_from_end(n: usize) -> NTS<CharAlphabet, bool, Void> {
    let mut ts = NTS::for_alphabet(CharAlphabet::of_size(2));
    for q in 0..=n {
        ts.add_state(q == n);
    }
    ts.add_edge((at(0), 'a', at(0)));
    ts.add_edge((at(0), 'b', at(0)));
    ts.add_edge((at(0), 'a', at(1)));
    for q in 1..n {
        ts.add_edge((at(q), 'a', at(q + 1)));
        ts.add_edge((at(q), 'b', at(q + 1)));
    }
    ts
}

/// A nondeterministic variant of [`scrambled`]: every state has the two successors of
/// [`scrambled`] with `k = 2` and `k = 3` on each of `a` and `b`.
pub fn scrambled_nts(n: usize) -> NTS<CharAlphabet, bool, Void> {
    let mut ts = NTS::for_alphabet(CharAlphabet::of_size(2));
    for q in 0..n {
        ts.add_state(q % 5 == 0);
    }
    for q in 0..n {
        for (i, sym) in ['a', 'b'].into_iter().enumerate() {
            ts.add_edge((at(q), sym, at((q * (2 * i + 3) + i + 1) % n)));
            ts.add_edge((at(q), sym, at((q * (2 * i + 5) + 3 * i + 2) % n)));
        }
    }
    ts
}

// ---------------------------------------------------------------------------------------------
// Automata over `CharAlphabet`
// ---------------------------------------------------------------------------------------------

/// A DFA over `k` symbols with `n` states and the structure of [`scrambled`].
pub fn dfa(n: usize, k: usize) -> DFA {
    scrambled(n, k).with_initial(at(0)).collect()
}

/// A DFA that is the minimal automaton of [`counter`].
pub fn counter_dfa(n: usize, k: usize) -> DFA {
    counter(n, k).with_initial(at(0)).collect()
}

/// A DFA with the structure of [`scrambled`] that accepts nothing, so that searching for an
/// accepted word has to visit every reachable state.
pub fn empty_dfa(n: usize, k: usize) -> DFA {
    build(
        n,
        k,
        |_| false,
        |q, i| {
            if i == 0 {
                (q + 1) % n
            } else {
                (q * (2 * i + 3) + 7 * i + 1) % n
            }
        },
    )
    .with_initial(at(0))
    .collect()
}

/// A DFA with the structure of [`scrambled`] in which only state `n - 1` accepts.
pub fn far_dfa(n: usize, k: usize) -> DFA {
    build(
        n,
        k,
        |q| q + 1 == n,
        |q, i| {
            if i == 0 {
                (q + 1) % n
            } else {
                (q * (2 * i + 3) + 7 * i + 1) % n
            }
        },
    )
    .with_initial(at(0))
    .collect()
}

/// The [`counter`] DFA in which in addition state `n - 1` accepts, hence it differs from
/// [`counter_dfa`] only on words that lead to the far end of the counter.
pub fn counter_dfa_with_far_state(n: usize, k: usize) -> DFA {
    build(n, k, |q| q == 0 || q + 1 == n, |q, i| (q + i + 1) % n)
        .with_initial(at(0))
        .collect()
}

/// A DFA that is not minimal, see [`redundant_counter`].
pub fn redundant_dfa(n: usize, k: usize) -> DFA {
    redundant_counter(n, k).with_initial(at(0)).collect()
}

/// A deterministic parity automaton with `n` states, `k` symbols and priorities `0..priorities`.
/// The priority of the edge `(q, i)` is `(q + 3 i) mod priorities` and the targets are
/// `(q * (2 i + 3) + 7 i + 1) mod n` as in [`fragmented`] with the first symbol going to `q + 1`.
/// Everything is one SCC that sees all priorities, so normalization has real work to do.
pub fn scrambled_dpa(n: usize, k: usize, priorities: Int) -> DPA {
    let mut ts: DTS<CharAlphabet, Void, Int> = DTS::for_alphabet(CharAlphabet::of_size(k));
    for _ in 0..n {
        ts.add_state(Void);
    }
    for q in 0..n {
        for (i, sym) in symbols(k).into_iter().enumerate() {
            let color = ((q + 3 * i) % priorities as usize) as Int;
            let target = if i == 0 {
                (q + 1) % n
            } else {
                (q * (2 * i + 3) + 7 * i + 1) % n
            };
            ts.add_edge((at(q), sym, color, at(target)));
        }
    }
    ts.with_initial(at(0)).collect()
}

/// A parity automaton in which the priority grows along a chain of `n` states that loops back
/// at the end: state `q` has priority `q mod priorities` on its first symbol and `0` on the
/// others. The unique SCC sees every priority, the acceptance is decided by the smallest.
pub fn chain_dpa(n: usize, priorities: Int) -> DPA {
    let mut ts: DTS<CharAlphabet, Void, Int> = DTS::for_alphabet(CharAlphabet::of_size(2));
    for _ in 0..n {
        ts.add_state(Void);
    }
    for q in 0..n {
        ts.add_edge((
            at(q),
            'a',
            (q % priorities as usize) as Int,
            at((q + 1) % n),
        ));
        ts.add_edge((at(q), 'b', 0, at(0)));
    }
    ts.with_initial(at(0)).collect()
}

// ---------------------------------------------------------------------------------------------
// Words
// ---------------------------------------------------------------------------------------------

/// A finite word of the given length over the first `k` symbols. The `i`-th symbol is
/// `(i * i + 3 i) / 2 mod k`, which is aperiodic enough to not stay on a short cycle.
pub fn word(len: usize, k: usize) -> String {
    let symbols = symbols(k);
    (0..len)
        .map(|i| symbols[((i * i + 3 * i) / 2) % k])
        .collect()
}

/// A finite word over the first `k` symbols from the Thue-Morse sequence.
pub fn thue_morse(len: usize, k: usize) -> String {
    let symbols = symbols(k);
    (0..len)
        .map(|i| symbols[(i.count_ones() as usize) % k.max(1)])
        .collect()
}

/// Ultimately periodic words `u v^ω` over `k` symbols with `|u| = spoke` and `|v| = cycle`.
pub fn lassos(count: usize, k: usize, spoke: usize, cycle: usize) -> Vec<(String, String)> {
    (0..count)
        .map(|i| {
            (
                thue_morse(spoke + i % 7, k),
                word(cycle + i % 5, k).chars().rev().collect(),
            )
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------------------------

/// A parity automaton read from a HOA fixture, over a propositional alphabet.
pub type FixtureDpa = DPA<DTS<PropAlphabet, Void, Int>>;

/// The fixtures that stem from LTL formulas, a selection of `benches/fixtures/ltl`.
///
/// Parsing HOA is slow (and valgrind makes it slower), and every benchmark parses its inputs
/// again because it runs in its own process. Hence benchmarks use selections of the fixtures,
/// chosen to differ in size and number of priorities. Automata with many atomic propositions are
/// avoided since every edge label is split into all valuations (see `benches/fixtures/README.md`)
/// and parsing time is proportional to the number of edges.
pub const LTL: &[&str] = &[
    "ltl/gh-r-3",
    "ltl/gh-q-3",
    "ltl/gf-equiv-3",
    "ltl/gf-implies-3",
    "ltl/go-theta-3",
    "ltl/rv-counter-3",
    "ltl/tv-uu-3",
    "ltl/u-left-3",
    "ltl/and-gf-3",
    "ltl/ms-phi-r-1",
    "ltl/ms-phi-s-1",
    "ltl/sejk-k-2",
    "ltl/lily-patterns-1",
    "ltl/sb-patterns-0",
    "ltl/eh-patterns-0",
];

/// Random and determinized fixtures, a selection of `benches/fixtures/{random,hard}`. Larger
/// and with more priorities than [`LTL`].
pub const SYNTHETIC: &[&str] = &[
    "random/n16-a1-p3-s1",
    "random/n64-a2-p4-s1",
    "random/n128-a2-p6-s1",
    "random/n256-a2-p8-s1",
    "hard/m-nba-3",
    "hard/l-nba-2",
    "hard/l-dsa-3",
];

/// Fixtures with 8 to 13 atomic propositions, `benches/fixtures/many_aps`. Everything in [`LTL`]
/// and [`SYNTHETIC`] has at most 5, so their edge labels fit into truth tables; these do not.
/// Separate so that the existing selections (and the history of their benchmarks) stay as they are.
pub const MANY_APS: &[&str] = &[
    "many_aps/and-gf-12",
    "many_aps/gf-equiv-12",
    "many_aps/r-right-10",
    "many_aps/random-n16-a8-p4-s1",
    "many_aps/random-n24-a12-p4-s1",
    "many_aps/random-n32-a16-p4-s1",
];
fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("benches/fixtures")
}

/// The text of a fixture, given as `directory/name`.
pub fn fixture_text(name: &str) -> String {
    std::fs::read_to_string(fixtures_dir().join(format!("{name}.hoa")))
        .unwrap_or_else(|e| panic!("cannot read fixture {name}: {e}"))
}

/// The texts of all fixtures in `names`, in that order.
pub fn fixture_texts(names: &[&str]) -> Vec<String> {
    names.iter().map(|name| fixture_text(name)).collect()
}

/// Parses a fixture into a parity automaton.
pub fn parse_dpa(text: &str) -> FixtureDpa {
    HoaString::from(text.to_string())
        .pop::<automata::ts::Det<automata::ts::Linked>>()
        .expect("fixture contains an automaton")
        .into_dpa()
        .expect("fixture is a parity automaton")
}

/// The parity automata of all fixtures in `names`.
pub fn fixture_dpas(names: &[&str]) -> Vec<FixtureDpa> {
    names
        .iter()
        .map(|name| parse_dpa(&fixture_text(name)))
        .collect()
}

pub fn ltl_dpas() -> Vec<FixtureDpa> {
    fixture_dpas(LTL)
}

pub fn synthetic_dpas() -> Vec<FixtureDpa> {
    fixture_dpas(SYNTHETIC)
}
pub fn many_aps_dpas() -> Vec<FixtureDpa> {
    fixture_dpas(MANY_APS)
}
/// Every DPA of [`MANY_APS`] together with its normalization, an equivalent automaton with
/// (usually) different colors, to compare against. Same inputs as `benches/versus`.
pub fn many_aps_pairs() -> Vec<(FixtureDpa, FixtureDpa)> {
    many_aps_dpas()
        .into_iter()
        .map(|dpa| {
            let other = dpa.normalized().collect();
            (dpa, other)
        })
        .collect()
}

/// A lasso over the symbols of the alphabet of a fixture. Symbols are chosen by an index
/// pattern, hence the word does not depend on anything but the alphabet.
pub fn fixture_lasso(
    alphabet: &PropAlphabet,
    spoke: usize,
    cycle: usize,
) -> ReducedOmegaWord<<PropAlphabet as automata::alphabet::Alphabet>::Symbol> {
    use automata::alphabet::Alphabet;
    let all: Vec<_> = alphabet.universe().collect();
    let pick = |len: usize, offset: usize| -> Vec<_> {
        (0..len)
            .map(|i| all[(i * i + offset) % all.len()])
            .collect()
    };
    ReducedOmegaWord::ultimately_periodic(pick(spoke, 1), pick(cycle, 2))
}

// ---------------------------------------------------------------------------------------------
// Nondeterministic omega automata
// ---------------------------------------------------------------------------------------------

/// A nondeterministic edge-colored system over `{a, b}` with `n` states: each state has two
/// successors per symbol, `(q * (2 i + 3) + i + 1) mod n` and `(q * (2 i + 5) + 3 i + 2) mod n`
/// as in [`scrambled_nts`], plus `q + 1` on `a` so that everything is one SCC. The edge to the
/// `j`-th successor on symbol `i` from `q` is colored with `color(q + 3 i + j)`.
pub fn scrambled_omega_nts<C: automata::Color>(
    n: usize,
    color: impl Fn(usize) -> C,
) -> NTS<CharAlphabet, Void, C> {
    let mut ts = NTS::for_alphabet(CharAlphabet::of_size(2));
    for _ in 0..n {
        ts.add_state(Void);
    }
    for q in 0..n {
        for (i, sym) in ['a', 'b'].into_iter().enumerate() {
            let targets = [
                (q * (2 * i + 3) + i + 1) % n,
                (q * (2 * i + 5) + 3 * i + 2) % n,
            ];
            for (j, target) in targets.into_iter().enumerate() {
                ts.add_edge((at(q), sym, color(q + 3 * i + j), at(target)));
            }
        }
        ts.add_edge((at(q), 'a', color(q + 2), at((q + 1) % n)));
    }
    ts
}

/// Parses a fixture with the nondeterministic storage, so that its semantics are existential.
pub fn parse_nondeterministic(
    text: &str,
) -> automata::automaton::NondeterministicOmegaAutomaton<PropAlphabet> {
    HoaString::from(text.to_string())
        .pop::<automata::ts::Linked>()
        .expect("fixture contains an automaton")
}
