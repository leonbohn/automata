//! Deterministic transition system generators shared by the benchmarks.
#![allow(dead_code)]

use automata::alphabet::CharAlphabet;
use automata::ts::{ForAlphabet, Sproutable};
use automata::{DTS, Int, NTS, Void};

/// Splitmix64, so that the benchmarks do not depend on `rand` and are reproducible.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }
}

/// Builds a deterministic TS over two symbols where `successor(q, i)` is the target of the
/// `i`-th symbol from state `q`. Every state is accepting iff `accepting(q)`.
fn build(
    n: usize,
    accepting: impl Fn(usize) -> bool,
    successor: impl Fn(usize, usize) -> usize,
) -> DTS<CharAlphabet, bool, Void> {
    let alphabet = CharAlphabet::of_size(2);
    let mut ts = DTS::for_alphabet(alphabet);
    for q in 0..n {
        ts.add_state(accepting(q));
    }
    for q in 0..n {
        for (i, sym) in ['a', 'b'].into_iter().enumerate() {
            ts.add_edge((q as u32, sym, successor(q, i) as u32));
        }
    }
    ts
}

/// Uniformly random successors; almost all states end up in one large SCC.
pub fn random_dts(n: usize, seed: u64) -> DTS<CharAlphabet, bool, Void> {
    let mut rng = Rng::new(seed);
    let table: Vec<[usize; 2]> = (0..n).map(|_| [rng.below(n), rng.below(n)]).collect();
    let colors: Vec<bool> = (0..n).map(|_| rng.below(2) == 0).collect();
    build(n, |q| colors[q], |q, i| table[q][i])
}

/// A single cycle `0 -> 1 -> ... -> n-1 -> 0`, hence one SCC and exactly one back edge.
pub fn ring(n: usize) -> DTS<CharAlphabet, bool, Void> {
    build(n, |q| q % 2 == 0, |q, _| (q + 1) % n)
}

/// A path `0 -> 1 -> ... -> n-1 -> 0` where in addition every state has an edge back to `0`.
/// There is one SCC and `n` back edges that all target the bottom of the DFS stack.
pub fn back_edges(n: usize) -> DTS<CharAlphabet, bool, Void> {
    build(
        n,
        |q| q % 2 == 0,
        |q, i| if i == 0 { (q + 1) % n } else { 0 },
    )
}

/// A path without any cycle (except for a self loop at the end): `n` singleton SCCs.
pub fn path(n: usize) -> DTS<CharAlphabet, bool, Void> {
    build(n, |q| q % 2 == 0, |q, _| (q + 1).min(n - 1))
}

/// Chains of 4-cycles, each of which jumps to the first state of the next one.
pub fn small_cycles(n: usize) -> DTS<CharAlphabet, bool, Void> {
    let n = n.next_multiple_of(4);
    build(
        n,
        |q| q % 3 == 0,
        |q, i| {
            let block = q / 4;
            if i == 0 {
                block * 4 + (q % 4 + 1) % 4
            } else if q % 4 == 3 {
                ((block + 1) * 4).min(n - 4)
            } else {
                block * 4 + (q % 4 + 1) % 4
            }
        },
    )
}

/// A random nondeterministic TS where each state has `degree` random successors per symbol.
pub fn random_nts(n: usize, degree: usize, seed: u64) -> NTS<CharAlphabet, bool, Void> {
    let mut rng = Rng::new(seed);
    let mut ts = NTS::for_alphabet(CharAlphabet::of_size(2));
    for q in 0..n {
        ts.add_state(q % 5 == 0);
    }
    for q in 0..n {
        for sym in ['a', 'b'] {
            for _ in 0..degree {
                ts.add_edge((q as u32, sym, rng.below(n) as u32));
            }
        }
    }
    ts
}

/// The symbols of an alphabet of size `k`.
pub fn symbols(k: usize) -> Vec<char> {
    ('a'..).take(k).collect()
}

/// A deterministic TS over `k` symbols with uniformly random successors and `Int` edge colors in
/// `0..priorities`. Use [`dpa`] to turn it into a parity automaton.
pub fn random_colored_dts(
    n: usize,
    k: usize,
    priorities: Int,
    seed: u64,
) -> DTS<CharAlphabet, Void, Int> {
    let mut rng = Rng::new(seed);
    let mut ts = DTS::for_alphabet(CharAlphabet::of_size(k));
    for _ in 0..n {
        ts.add_state(Void);
    }
    for q in 0..n {
        for sym in symbols(k) {
            let color = rng.below(priorities as usize) as Int;
            ts.add_edge((q as u32, sym, color, rng.below(n) as u32));
        }
    }
    ts
}

/// A random deterministic parity automaton with `n` states, two symbols and four priorities.
pub fn dpa(n: usize, seed: u64) -> automata::automaton::DPA {
    use automata::representation::IntoTs;
    random_colored_dts(n, 2, 4, seed).into_dpa_with_initial(0)
}

/// An NFA over `{a, b}` accepting the words whose `n`-th symbol from the end is `a`. Its subset
/// construction has `2^n` reachable states, so it does not collapse like random NFAs do.
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

/// A deterministic TS with `n` states and `k` symbols, uniformly random successors.
pub fn random_dts_over(n: usize, k: usize, seed: u64) -> DTS<CharAlphabet, bool, Void> {
    let mut rng = Rng::new(seed);
    let mut ts = DTS::for_alphabet(CharAlphabet::of_size(k));
    for q in 0..n {
        ts.add_state(q % 2 == 0);
    }
    for q in 0..n {
        for sym in symbols(k) {
            ts.add_edge((q as u32, sym, rng.below(n) as u32));
        }
    }
    ts
}

/// `count` random words over the first `k` symbols with a length in `min..=max`.
pub fn random_words(count: usize, k: usize, min: usize, max: usize, seed: u64) -> Vec<String> {
    let mut rng = Rng::new(seed);
    let symbols = symbols(k);
    (0..count)
        .map(|_| {
            let len = min + rng.below(max - min + 1);
            (0..len).map(|_| symbols[rng.below(k)]).collect()
        })
        .collect()
}
