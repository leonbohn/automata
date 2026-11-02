//! Property tests for the operations on the different kinds of automata. Automata are drawn as
//! complete deterministic systems over a small alphabet, the language-level properties are then
//! checked both on sampled words and with the language problems (emptiness, inclusion, ...), so
//! that a bug in either side is noticed.

use automata::{
    Pointed, TransitionSystem,
    automaton::{
        DBA, DFA, DPA, Disjointness, Emptiness, Equivalence, Inclusion, MealyMachine, MooreMachine,
    },
    representation::CollectPointed,
    ts::{Builder, States},
    word::ReducedOmegaWord,
};
use proptest::prelude::*;

const MAX_STATES: usize = 6;
const MAX_SYMBOLS: usize = 3;
const MAX_PRIORITY: u8 = 4;

/// A complete transition table: `table[q][a]` is the target of `q` on the `a`-th symbol, with
/// `col` being the color of that edge.
#[derive(Debug, Clone)]
struct Table {
    symbols: usize,
    /// `(target, color)` for every state and symbol.
    edges: Vec<Vec<(u32, u8)>>,
    /// one color per state
    state_colors: Vec<u8>,
}

impl Table {
    fn edges(&self) -> impl Iterator<Item = (u32, char, u8, u32)> + '_ {
        self.edges.iter().enumerate().flat_map(|(q, row)| {
            row.iter()
                .enumerate()
                .map(move |(a, &(t, c))| (q as u32, (b'a' + a as u8) as char, c, t))
        })
    }

    fn plain_edges(&self) -> impl Iterator<Item = (u32, char, u32)> + '_ {
        self.edges().map(|(q, a, _, t)| (q, a, t))
    }
}

fn table(max_color: u8) -> impl Strategy<Value = Table> {
    (1..=MAX_STATES, 1..=MAX_SYMBOLS).prop_flat_map(move |(n, k)| {
        (
            Just(k),
            prop::collection::vec(prop::collection::vec((0..n as u32, 0..=max_color), k), n),
            prop::collection::vec(0..=max_color, n),
        )
            .prop_map(|(symbols, edges, state_colors)| Table {
                symbols,
                edges,
                state_colors,
            })
    })
}

fn dfa() -> impl Strategy<Value = DFA> {
    table(1).prop_map(|t| {
        DFA::builder()
            .with_state_colors(t.state_colors.iter().map(|&c| c == 1))
            .with_edges(t.plain_edges())
            .into_dfa(0)
    })
}

/// A pair of DFAs over the same alphabet.
fn dfa_pair() -> impl Strategy<Value = (DFA, DFA)> {
    (1..=MAX_SYMBOLS).prop_flat_map(|k| {
        let one = move || {
            table(1)
                .prop_filter("alphabet size", move |t| t.symbols == k)
                .prop_map(|t| {
                    DFA::builder()
                        .with_state_colors(t.state_colors.iter().map(|&c| c == 1))
                        .with_edges(t.plain_edges())
                        .into_dfa(0)
                })
        };
        (one(), one())
    })
}

fn dpa() -> impl Strategy<Value = DPA> {
    table(MAX_PRIORITY).prop_map(|t| {
        Builder::without_state_colors()
            .with_edges(t.edges())
            .into_dpa(0)
    })
}

/// A DBA together with the DPA that has priority 0 on the accepting edges and 1 on the others.
fn dba_and_dpa() -> impl Strategy<Value = (DBA, DPA)> {
    table(1).prop_map(|t| {
        let dba = Builder::without_state_colors()
            .with_edges(t.edges().map(|(q, a, c, t)| (q, a, c == 1, t)))
            .into_dba(0);
        let dpa = Builder::without_state_colors()
            .with_edges(t.edges().map(|(q, a, c, t)| (q, a, 1 - c, t)))
            .into_dpa(0);
        (dba, dpa)
    })
}

fn dba() -> impl Strategy<Value = DBA> {
    dba_and_dpa().prop_map(|(dba, _)| dba)
}

fn moore() -> impl Strategy<Value = MooreMachine> {
    table(MAX_PRIORITY).prop_map(|t| {
        Builder::without_edge_colors()
            .with_state_colors(t.state_colors.iter().copied())
            .with_edges(t.plain_edges())
            .into_moore(0)
    })
}

fn mealy() -> impl Strategy<Value = MealyMachine> {
    table(MAX_PRIORITY).prop_map(|t| {
        Builder::without_state_colors()
            .with_edges(t.edges())
            .into_mealy(0)
    })
}

/// Words over the symbols `a`, `b`, `c`; symbols outside the alphabet are filtered by the
/// caller via [`restrict`].
fn raw_word(max_len: usize) -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(0u8..MAX_SYMBOLS as u8, 0..=max_len)
}

fn restrict(word: &[u8], symbols: usize) -> Vec<char> {
    word.iter()
        .map(|&a| (b'a' + (a % symbols as u8)) as char)
        .collect()
}

fn finite_words() -> impl Strategy<Value = Vec<Vec<u8>>> {
    prop::collection::vec(raw_word(8), 1..24)
}

/// Ultimately periodic words given by a prefix and a non-empty loop.
fn lassos() -> impl Strategy<Value = Vec<(Vec<u8>, Vec<u8>)>> {
    prop::collection::vec(
        (
            raw_word(4),
            prop::collection::vec(0u8..MAX_SYMBOLS as u8, 1..=4),
        ),
        1..24,
    )
}

fn lasso(prefix: &[u8], cycle: &[u8], symbols: usize) -> ReducedOmegaWord<char> {
    let mut repr = restrict(prefix, symbols);
    let loop_index = repr.len();
    repr.extend(restrict(cycle, symbols));
    ReducedOmegaWord::from_raw_parts(repr, loop_index)
}

fn symbols_of<T: TransitionSystem>(ts: &T) -> usize {
    ts.symbols().count()
}

proptest! {
    // ---- DFA -----------------------------------------------------------------------------

    #[test]
    fn dfa_minimization_keeps_language(a in dfa(), words in finite_words()) {
        let k = symbols_of(&a);
        let min = a.clone().minimize();
        prop_assert!(min.state_count() <= a.state_count());
        prop_assert!(Equivalence::of(&a).and(&min).holds());
        for w in &words {
            let w = restrict(w, k);
            prop_assert_eq!(a.accepts(&w), min.accepts(&w));
        }
    }

    #[test]
    fn dfa_minimization_is_idempotent(a in dfa()) {
        let min = a.minimize();
        let again = min.clone().minimize();
        prop_assert_eq!(min.state_count(), again.state_count());
    }

    #[test]
    fn dfa_equivalent_dfas_have_equally_large_minimizations((a, b) in dfa_pair()) {
        if Equivalence::of(&a).and(&b).holds() {
            // minimization keeps unreachable states, so they are removed first
            let trim = |d: DFA| d.reachable_part().collect_dfa().minimize().state_count();
            prop_assert_eq!(trim(a), trim(b));
        }
    }

    #[test]
    fn dfa_union_with_complement_is_universal(a in dfa(), words in finite_words()) {
        let k = symbols_of(&a);
        let neg = a.as_ref().negation().reachable_part().collect_dfa();
        let union = a.as_ref().union(&neg).reachable_part().collect_dfa();
        prop_assert!(Emptiness::of(&union.negation().reachable_part().collect_dfa()).holds());
        for w in &words {
            prop_assert!(union.accepts(restrict(w, k)));
        }
    }

    #[test]
    fn dfa_intersection_with_complement_is_empty(a in dfa(), words in finite_words()) {
        let k = symbols_of(&a);
        let neg = a.as_ref().negation().reachable_part().collect_dfa();
        let inter = a.as_ref().intersection(&neg).reachable_part().collect_dfa();
        prop_assert!(Emptiness::of(&inter).holds());
        prop_assert!(Disjointness::of(&a).and(&neg).holds());
        for w in &words {
            prop_assert!(!inter.accepts(restrict(w, k)));
        }
    }

    #[test]
    fn dfa_double_negation_is_identity(a in dfa()) {
        let neg = a.as_ref().negation().reachable_part().collect_dfa();
        let back = neg.as_ref().negation().reachable_part().collect_dfa();
        prop_assert!(Equivalence::of(&a).and(&back).holds());
    }

    #[test]
    fn dfa_de_morgan((a, b) in dfa_pair(), words in finite_words()) {
        let k = symbols_of(&a);
        let (na, nb) = (
            a.as_ref().negation().reachable_part().collect_dfa(),
            b.as_ref().negation().reachable_part().collect_dfa(),
        );
        let union = a.as_ref().union(&b).reachable_part().collect_dfa();
        let inter = a.as_ref().intersection(&b).reachable_part().collect_dfa();
        let lhs = union.negation().reachable_part().collect_dfa();
        let rhs = na.as_ref().intersection(&nb).reachable_part().collect_dfa();
        prop_assert!(Equivalence::of(&lhs).and(&rhs).holds());
        // the operations agree with the boolean operations on the acceptance of single words
        for w in &words {
            let w = restrict(w, k);
            prop_assert_eq!(union.accepts(&w), a.accepts(&w) || b.accepts(&w));
            prop_assert_eq!(inter.accepts(&w), a.accepts(&w) && b.accepts(&w));
        }
        // intersection is below both arguments, union is above both
        prop_assert!(Inclusion::of(&inter).within(&a).holds());
        prop_assert!(Inclusion::of(&a).within(&union).holds());
        prop_assert!(Inclusion::of(&b).within(&union).holds());
    }

    #[test]
    fn dfa_problem_witnesses_are_valid((a, b) in dfa_pair()) {
        if let Some(w) = Emptiness::of(&a).witness() {
            prop_assert!(a.accepts(&w));
        }
        if let Some(w) = Inclusion::of(&a).within(&b).counterexample() {
            prop_assert!(a.accepts(&w) && !b.accepts(&w));
        }
        if let Some(w) = Equivalence::of(&a).and(&b).counterexample() {
            prop_assert!(a.accepts(&w) != b.accepts(&w));
        }
        if let Some(w) = Disjointness::of(&a).and(&b).witness() {
            prop_assert!(a.accepts(&w) && b.accepts(&w));
        }
        prop_assert!(Equivalence::of(&a).and(&a).holds());
    }

    // ---- DPA -----------------------------------------------------------------------------

    #[test]
    fn dpa_complement_flips_acceptance(a in dpa(), words in lassos()) {
        let k = symbols_of(&a);
        let complement = a.clone().complement();
        for (p, c) in &words {
            let w = lasso(p, c, k);
            prop_assert_eq!(a.accepts(&w), !complement.accepts(&w));
        }
    }

    #[test]
    fn dpa_complement_is_disjoint_and_covering(a in dpa()) {
        let complement = a.clone().complement();
        // nothing is in both: the language of `a` is inside `a`'s complement iff it is empty
        prop_assert_eq!(
            Inclusion::of(&a).within(&complement).holds(),
            Emptiness::of(&a).holds()
        );
        // everything is in one: the complement of the complement is `a` again
        prop_assert!(Equivalence::of(&a).and(&complement.complement()).holds());
        prop_assert!(!Equivalence::of(&a).and(&a.clone().complement()).holds());
    }

    #[test]
    fn dpa_normalization_keeps_language(a in dpa(), words in lassos()) {
        let k = symbols_of(&a);
        let normalized = a.normalized();
        prop_assert!(Equivalence::of(&a).and(&normalized).holds());
        for (p, c) in &words {
            let w = lasso(p, c, k);
            prop_assert_eq!(a.accepts(&w), normalized.accepts(&w));
        }
    }

    #[test]
    fn dpa_problem_witnesses_are_valid(a in dpa(), b in dpa()) {
        prop_assume!(symbols_of(&a) == symbols_of(&b));
        if let Some(w) = Emptiness::of(&a).witness() {
            prop_assert!(a.accepts(&w));
        }
        if let Some(w) = Inclusion::of(&a).within(&b).counterexample() {
            prop_assert!(a.accepts(&w) && !b.accepts(&w));
        }
        if let Some(w) = Equivalence::of(&a).and(&b).counterexample() {
            prop_assert!(a.accepts(&w) != b.accepts(&w));
        }
        prop_assert!(Equivalence::of(&a).and(&a).holds());
    }

    // ---- DBA -----------------------------------------------------------------------------

    #[test]
    fn dba_witness_is_accepted(a in dba(), words in lassos()) {
        let k = symbols_of(&a);
        let witness = Emptiness::of(&a).witness();
        if let Some(w) = &witness {
            prop_assert!(a.accepts(w));
        } else {
            // an empty language accepts none of the sampled words
            for (p, c) in &words {
                prop_assert!(!a.accepts(lasso(p, c, k)));
            }
        }
    }

    #[test]
    fn dba_as_dpa_has_same_language((a, dpa) in dba_and_dpa(), words in lassos()) {
        let k = symbols_of(&a);
        prop_assert_eq!(Emptiness::of(&a).holds(), Emptiness::of(&dpa).holds());
        for (p, c) in &words {
            let w = lasso(p, c, k);
            prop_assert_eq!(a.accepts(&w), dpa.accepts(&w));
        }
    }

    // ---- Moore and Mealy machines --------------------------------------------------------

    #[test]
    fn moore_minimization_keeps_outputs(m in moore(), words in finite_words()) {
        let k = symbols_of(&m);
        let min = m.minimize();
        prop_assert!(m.bisimilar(&min));
        prop_assert!(min.state_count() <= m.state_count());
        prop_assert_eq!(min.state_count(), min.minimize().state_count());
        for w in &words {
            let w = restrict(w, k);
            prop_assert_eq!(m.map(&w), min.map(&w));
        }
    }

    #[test]
    fn moore_bisimilarity_witness_separates(m in moore(), n in moore()) {
        prop_assume!(symbols_of(&m) == symbols_of(&n));
        match m.witness_non_bisimilarity(&n) {
            Some(w) => prop_assert!(m.map(&w) != n.map(&w)),
            None => prop_assert!(m.bisimilar(&n)),
        }
        prop_assert!(m.bisimilar(&m));
    }

    #[test]
    fn mealy_minimization_keeps_outputs(m in mealy(), words in finite_words()) {
        let k = symbols_of(&m);
        let min = m.minimize();
        prop_assert!(m.bisimilar(&min));
        prop_assert!(min.state_count() <= m.state_count());
        for w in &words {
            let w = restrict(w, k);
            if w.is_empty() {
                continue;
            }
            prop_assert_eq!(m.transform(&w), min.transform(&w));
        }
    }

    #[test]
    fn mealy_inequivalence_witness_separates(m in mealy(), n in mealy()) {
        prop_assume!(symbols_of(&m) == symbols_of(&n));
        if let Some(w) = m.witness_inequivalence(&n) {
            prop_assert!(m.transform(&w) != n.transform(&w));
        }
        prop_assert!(m.bisimilar(&m));
    }
}

#[cfg(feature = "hoa")]
mod hoa {
    use super::*;
    use automata::{
        alphabet::PropSymbol,
        hoa::{HoaString, WriteHoa},
        ts::{Det, Linked},
        word::OmegaWord,
    };

    /// Converts a word over `a, b, c, ..` to one over the propositional alphabet read from HOA.
    /// The letter with index `i` is written as the valuation in which only proposition `i` holds.
    fn to_prop(aps: usize, w: &ReducedOmegaWord<char>) -> ReducedOmegaWord<PropSymbol> {
        let symbol = |c: char| {
            PropSymbol::from_bools((0..aps).map(|i| i == (c as u8 - b'a') as usize).collect())
        };
        let mut repr: Vec<_> = w.spoke().iter().map(|&c| symbol(c)).collect();
        let loop_index = repr.len();
        repr.extend(w.cycle().iter().map(|&c| symbol(c)));
        ReducedOmegaWord::from_raw_parts(repr, loop_index)
    }

    proptest! {
        #[test]
        fn dpa_hoa_round_trip_keeps_language(a in dpa(), words in lassos()) {
            let k = symbols_of(&a);
            let text = a.to_hoa().expect("every DPA over a char alphabet is writable");
            let parsed = HoaString::from(text.clone())
                .pop::<Det<Linked>>()
                .expect("written HOA is readable");
            prop_assert_eq!(parsed.state_count(), a.state_count());
                        let back = parsed.into_dpa().expect("parity stays parity");
            for (p, c) in &words {
                let w = lasso(p, c, k);
                prop_assert_eq!(a.accepts(&w), back.accepts(to_prop(k, &w)), "{}", text);
            }
            // writing what was read gives back the same HOA, up to the order of the edges
            let sorted = |hoa: &str| {
                let mut lines: Vec<_> = hoa.lines().map(str::to_string).collect();
                lines.sort();
                lines
            };
            prop_assert_eq!(sorted(&back.to_hoa().unwrap()), sorted(&text));
        }

        #[test]
        fn dba_hoa_round_trip_keeps_language(a in dba(), words in lassos()) {
            let k = symbols_of(&a);
            let text = a.to_hoa().expect("every DBA over a char alphabet is writable");
            let parsed = HoaString::from(text.clone())
                .pop::<Det<Linked>>()
                .expect("written HOA is readable");
                        let back = parsed.into_dpa().expect("Büchi converts to parity");
            for (p, c) in &words {
                let w = lasso(p, c, k);
                prop_assert_eq!(a.accepts(&w), back.accepts(to_prop(k, &w)), "{}", text);
            }
        }
    }
}
