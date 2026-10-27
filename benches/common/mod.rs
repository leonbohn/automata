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
use automata::ts::{ForAlphabet, Sproutable};
use automata::word::ReducedOmegaWord;
use automata::{DTS, Int, NTS, Void};

/// A DTS with boolean state colors and no edge colors, the shape a [`DFA`] is made from.
pub type Dts = DTS<CharAlphabet, bool, Void>;

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
            ts.add_edge((q as u32, sym, successor(q, i) as u32));
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
    ts.add_edge((0, 'a', 0));
    ts.add_edge((0, 'b', 0));
    ts.add_edge((0, 'a', 1));
    for q in 1..n {
        ts.add_edge((q as u32, 'a', q as u32 + 1));
        ts.add_edge((q as u32, 'b', q as u32 + 1));
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
            ts.add_edge((q as u32, sym, ((q * (2 * i + 3) + i + 1) % n) as u32));
            ts.add_edge((q as u32, sym, ((q * (2 * i + 5) + 3 * i + 2) % n) as u32));
        }
    }
    ts
}

// ---------------------------------------------------------------------------------------------
// Automata over `CharAlphabet`
// ---------------------------------------------------------------------------------------------

/// A DFA over `k` symbols with `n` states and the structure of [`scrambled`].
pub fn dfa(n: usize, k: usize) -> DFA {
    use automata::representation::IntoTs;
    scrambled(n, k).into_dfa_with_initial(0)
}

/// A DFA that is the minimal automaton of [`counter`].
pub fn counter_dfa(n: usize, k: usize) -> DFA {
    use automata::representation::IntoTs;
    counter(n, k).into_dfa_with_initial(0)
}

/// A DFA with the structure of [`scrambled`] that accepts nothing, so that searching for an
/// accepted word has to visit every reachable state.
pub fn empty_dfa(n: usize, k: usize) -> DFA {
    use automata::representation::IntoTs;
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
    .into_dfa_with_initial(0)
}

/// A DFA with the structure of [`scrambled`] in which only state `n - 1` accepts.
pub fn far_dfa(n: usize, k: usize) -> DFA {
    use automata::representation::IntoTs;
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
    .into_dfa_with_initial(0)
}

/// The [`counter`] DFA in which in addition state `n - 1` accepts, hence it differs from
/// [`counter_dfa`] only on words that lead to the far end of the counter.
pub fn counter_dfa_with_far_state(n: usize, k: usize) -> DFA {
    use automata::representation::IntoTs;
    build(n, k, |q| q == 0 || q + 1 == n, |q, i| (q + i + 1) % n).into_dfa_with_initial(0)
}

/// A DFA that is not minimal, see [`redundant_counter`].
pub fn redundant_dfa(n: usize, k: usize) -> DFA {
    use automata::representation::IntoTs;
    redundant_counter(n, k).into_dfa_with_initial(0)
}

/// A deterministic parity automaton with `n` states, `k` symbols and priorities `0..priorities`.
/// The priority of the edge `(q, i)` is `(q + 3 i) mod priorities` and the targets are
/// `(q * (2 i + 3) + 7 i + 1) mod n` as in [`fragmented`] with the first symbol going to `q + 1`.
/// Everything is one SCC that sees all priorities, so normalization has real work to do.
pub fn scrambled_dpa(n: usize, k: usize, priorities: Int) -> DPA {
    use automata::representation::IntoTs;
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
            ts.add_edge((q as u32, sym, color, target as u32));
        }
    }
    ts.into_dpa_with_initial(0)
}

/// A parity automaton in which the priority grows along a chain of `n` states that loops back
/// at the end: state `q` has priority `q mod priorities` on its first symbol and `0` on the
/// others. The unique SCC sees every priority, the acceptance is decided by the smallest.
pub fn chain_dpa(n: usize, priorities: Int) -> DPA {
    use automata::representation::IntoTs;
    let mut ts: DTS<CharAlphabet, Void, Int> = DTS::for_alphabet(CharAlphabet::of_size(2));
    for _ in 0..n {
        ts.add_state(Void);
    }
    for q in 0..n {
        ts.add_edge((
            q as u32,
            'a',
            (q % priorities as usize) as Int,
            ((q + 1) % n) as u32,
        ));
        ts.add_edge((q as u32, 'b', 0, 0u32));
    }
    ts.into_dpa_with_initial(0)
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
pub type FixtureDpa = DPA<PropAlphabet>;

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
        .pop::<true>()
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
