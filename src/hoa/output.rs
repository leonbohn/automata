use crate::automaton::{
    AcceptanceMask, Automaton, BuchiCondition, CoBuchiCondition, MaxEvenParityCondition,
    MaxOddParityCondition, MinEvenParityCondition, MinOddParityCondition, OmegaAcceptanceCondition,
    ParityKind, RabinCondition, RabinPair,
};
use crate::ts::States;
use itertools::Itertools;
use tracing::trace;

use std::collections::BTreeSet;
use std::fmt::Write;

use super::HoaError;
use crate::{
    Int, Pointed,
    alphabet::{Alphabet, CharAlphabet, PropAlphabet},
    ts::{DenseId, EdgeColor},
};

/// Acceptance conditions that can be written in the [HOA format](https://adl.github.io/hoaf/)
/// for the transition system `T`. This is what the [`WriteHoa`] implementation of
/// [`Automaton`] delegates to: the condition decides how the `acc-name` and `Acceptance`
/// header items look and which acceptance sets an edge belongs to.
pub trait HoaAcceptance<T: States> {
    /// Writes the `acc-name` (if any) and `Acceptance` header items, each terminated by a
    /// newline. The transition system is passed because some conditions (the parity conditions
    /// of a [`crate::automaton::DPA`]) derive their range from the edge colors.
    ///
    /// # Errors
    /// [`HoaError::UnsupportedAcceptance`] if the condition cannot be written, or
    /// [`HoaError::Format`] if the writer fails.
    fn write_acceptance<W: Write>(&self, ts: &T, w: &mut W) -> Result<(), HoaError>;

    /// Writes the acceptance sets that an edge with the given color belongs to, as a space
    /// followed by the sets in braces. Nothing is written if the edge belongs to no set.
    fn write_edge_color<W: Write>(&self, color: &EdgeColor<T>, w: &mut W) -> Result<(), HoaError>;
}

/// Automata that can be written in the HOA format.
pub trait WriteHoa {
    /// Writes the automaton in the HOA format to the given writer.
    ///
    /// # Errors
    /// Fails if the acceptance condition cannot be written or if the writer fails.
    fn write_hoa<W: Write>(&self, w: &mut W) -> Result<(), HoaError>;

    /// Returns the automaton in the HOA format as a string.
    ///
    /// # Errors
    /// See [`Self::write_hoa`].
    fn to_hoa(&self) -> Result<String, HoaError> {
        let mut w = String::new();
        self.write_hoa(&mut w)?;
        trace!("produced HOA string from automaton\n{}", w);
        Ok(w)
    }
}

impl<T, Z> WriteHoa for Automaton<T, Z>
where
    T: States<StateIndex: DenseId>,
    T::Alphabet: HoaSuitableAlphabet,
    Z: HoaAcceptance<T>,
{
    fn write_hoa<W: Write>(&self, w: &mut W) -> Result<(), HoaError> {
        let ts = self.ts();
        w.write_str("HOA: v1\n")?;
        ts.alphabet().write_alphabet_description(w)?;
        writeln!(w, "States: {}", ts.state_count())?;
        writeln!(w, "Start: {}", self.initial().into_usize())?;
        self.acceptance().write_acceptance(ts, w)?;
        w.write_str("--BODY--")?;
        for state in ts.states() {
            write!(w, "\nState: {}", state.into_usize())?;
            for edge in ts.edges_from(state).into_iter().flatten() {
                w.write_str("\n[")?;
                ts.alphabet().write_expression(w, edge.expression())?;
                write!(w, "] {}", edge.target().into_usize())?;
                self.acceptance().write_edge_color(edge.color(), w)?;
            }
        }
        w.write_str("\n--END--\n")?;
        Ok(())
    }
}

/// Written like a nondeterministic automaton, the promise of history-determinism is not recorded.
impl<T: States, C: HoaAcceptance<T>> HoaAcceptance<T>
    for crate::automaton::HistoryDeterministic<C>
{
    fn write_acceptance<W: Write>(&self, ts: &T, w: &mut W) -> Result<(), HoaError> {
        self.0.write_acceptance(ts, w)
    }

    fn write_edge_color<W: Write>(&self, color: &T::EdgeColor, w: &mut W) -> Result<(), HoaError> {
        self.0.write_edge_color(color, w)
    }
}

/// A nondeterministic automaton is written like a deterministic one, HOA does not distinguish them.
impl<T: States, C: HoaAcceptance<T>> HoaAcceptance<T> for crate::automaton::Existential<C> {
    fn write_acceptance<W: Write>(&self, ts: &T, w: &mut W) -> Result<(), HoaError> {
        self.0.write_acceptance(ts, w)
    }

    fn write_edge_color<W: Write>(&self, color: &T::EdgeColor, w: &mut W) -> Result<(), HoaError> {
        self.0.write_edge_color(color, w)
    }
}

impl<T: States<EdgeColor = bool>> HoaAcceptance<T> for BuchiCondition {
    fn write_acceptance<W: Write>(&self, _ts: &T, w: &mut W) -> Result<(), HoaError> {
        Ok(write_buchi_hoa(w)?)
    }

    fn write_edge_color<W: Write>(&self, color: &bool, w: &mut W) -> Result<(), HoaError> {
        if *color {
            w.write_str(" {0}")?;
        }
        Ok(())
    }
}

impl<T: States<EdgeColor = bool>> HoaAcceptance<T> for CoBuchiCondition {
    fn write_acceptance<W: Write>(&self, _ts: &T, w: &mut W) -> Result<(), HoaError> {
        Ok(write_co_buchi_hoa(w)?)
    }

    fn write_edge_color<W: Write>(&self, color: &bool, w: &mut W) -> Result<(), HoaError> {
        if *color {
            w.write_str(" {0}")?;
        }
        Ok(())
    }
}

/// Every edge belongs to the one acceptance set that is its color, the pairs refer to these sets.
impl<T: States<EdgeColor = Int>> HoaAcceptance<T> for RabinCondition<Int> {
    fn write_acceptance<W: Write>(&self, ts: &T, w: &mut W) -> Result<(), HoaError> {
        let pairs: Vec<_> = self.pairs().cloned().collect();
        let edge_sets = ts
            .states()
            .flat_map(|q| ts.edges_from(q).into_iter().flatten())
            .map(|edge| usize::from(*edge.color()) + 1)
            .max()
            .unwrap_or(0);
        Ok(write_pairs_hoa(
            w, "Rabin", &pairs, edge_sets, " | ", "f", " & ",
        )?)
    }

    fn write_edge_color<W: Write>(&self, color: &Int, w: &mut W) -> Result<(), HoaError> {
        Ok(write!(w, " {{{color}}}")?)
    }
}

/// The typed parity conditions write the sets `0..=high`, where `high` is the greatest color on
/// an edge.
macro_rules! typed_parity_hoa {
    ($cond:ty, $kind:expr) => {
        impl<T: States<EdgeColor = Int>> HoaAcceptance<T> for $cond {
            fn write_acceptance<W: Write>(&self, ts: &T, w: &mut W) -> Result<(), HoaError> {
                let high = ts
                    .states()
                    .flat_map(|q| ts.edges_from(q).into_iter().flatten())
                    .map(|edge| *edge.color())
                    .max()
                    .unwrap_or(0);
                Ok(write_parity_hoa(w, $kind, high)?)
            }

            fn write_edge_color<W: Write>(&self, color: &Int, w: &mut W) -> Result<(), HoaError> {
                Ok(write!(w, " {{{color}}}")?)
            }
        }
    };
}
typed_parity_hoa!(MinEvenParityCondition, ParityKind::MinEven);
typed_parity_hoa!(MaxEvenParityCondition, ParityKind::MaxEven);
typed_parity_hoa!(MinOddParityCondition, ParityKind::MinOdd);
typed_parity_hoa!(MaxOddParityCondition, ParityKind::MaxOdd);

impl<T: States<EdgeColor = AcceptanceMask>> HoaAcceptance<T> for OmegaAcceptanceCondition {
    fn write_acceptance<W: Write>(&self, ts: &T, w: &mut W) -> Result<(), HoaError> {
        let edge_sets = |ts: &T| {
            ts.states()
                .flat_map(|q| ts.edges_from(q).into_iter().flatten())
                .filter_map(|edge| edge.color().max())
                .map(|set| usize::from(set) + 1)
                .max()
                .unwrap_or(0)
        };
        match self {
            OmegaAcceptanceCondition::Parity(kind, _, high) => {
                Ok(write_parity_hoa(w, *kind, *high)?)
            }
            OmegaAcceptanceCondition::Buchi | OmegaAcceptanceCondition::Reachability => {
                Ok(write_buchi_hoa(w)?)
            }
            OmegaAcceptanceCondition::CoBuchi | OmegaAcceptanceCondition::Safety => {
                Ok(write_co_buchi_hoa(w)?)
            }
            OmegaAcceptanceCondition::Rabin(pairs) => Ok(write_pairs_hoa(
                w,
                "Rabin",
                pairs,
                edge_sets(ts),
                " | ",
                "f",
                " & ",
            )?),
            OmegaAcceptanceCondition::Streett(pairs) => Ok(write_pairs_hoa(
                w,
                "Streett",
                pairs,
                edge_sets(ts),
                " & ",
                "t",
                " | ",
            )?),
        }
    }

    fn write_edge_color<W: Write>(&self, mask: &AcceptanceMask, w: &mut W) -> Result<(), HoaError> {
        if mask.iter().next().is_some() {
            write!(w, " {{{}}}", mask.iter().join(" "))?;
        }
        Ok(())
    }
}

fn write_buchi_hoa<W: Write>(w: &mut W) -> std::fmt::Result {
    write!(w, "acc-name: Buchi\nAcceptance: 1 Inf(0)\n")
}

fn write_co_buchi_hoa<W: Write>(w: &mut W) -> std::fmt::Result {
    write!(w, "acc-name: co-Buchi\nAcceptance: 1 Fin(0)\n")
}

/// Writes a parity condition over the acceptance sets `0..=high`. The edges are labeled with their
/// priorities as they are, so the sets are `0..=high` even if the sets below the least priority
/// are unused.
fn write_parity_hoa<W: Write>(w: &mut W, kind: ParityKind, high: Int) -> std::fmt::Result {
    let sets = usize::from(high) + 1;
    let order: Vec<Int> = if kind.is_max() {
        (0..=high).rev().collect()
    } else {
        (0..=high).collect()
    };
    write!(
        w,
        "acc-name: parity {} {} {sets}\nAcceptance: {sets} {}\n",
        if kind.is_max() { "max" } else { "min" },
        if kind.is_even() { "even" } else { "odd" },
        build_parity_condition_hoa(&order, kind.is_even())
    )
}

/// Writes a Rabin or Streett condition. A pair is `Fin(..) <pair_op> Inf(..)`, the pairs are
/// joined by `pair_join`, `empty` is the condition without pairs. At least `edge_sets` acceptance
/// sets are declared, so that all sets that edges belong to exist.
fn write_pairs_hoa<W: Write>(
    w: &mut W,
    name: &str,
    pairs: &[RabinPair<Int>],
    edge_sets: usize,
    pair_join: &str,
    empty: &str,
    pair_op: &str,
) -> std::fmt::Result {
    // `acc-name: Rabin n` promises that pair `i` is `Fin(2i)`, `Inf(2i + 1)`
    let standard = pairs.iter().enumerate().all(|(i, p)| {
        let i = (2 * i) as Int;
        p.fin.iter().eq([&i]) && p.inf.iter().eq([&(i + 1)])
    });
    let sets = pairs
        .iter()
        .flat_map(|p| p.fin.iter().chain(&p.inf))
        .max()
        .map_or(0, |m| usize::from(*m) + 1)
        .max(edge_sets);
    if standard && sets == 2 * pairs.len() {
        writeln!(w, "acc-name: {name} {}", pairs.len())?;
    }
    let term = |set: &BTreeSet<Int>, name: &str, op: &str, none: &str| {
        if set.is_empty() {
            none.to_string()
        } else {
            set.iter().map(|i| format!("{name}({i})")).join(op)
        }
    };
    let formula = if pairs.is_empty() {
        empty.to_string()
    } else {
        pairs
            .iter()
            .map(|p| {
                format!(
                    "({}){pair_op}({})",
                    term(&p.fin, "Fin", " & ", "t"),
                    term(&p.inf, "Inf", " | ", "f")
                )
            })
            .join(pair_join)
    };
    writeln!(w, "Acceptance: {sets} {formula}")
}

/// Alphabets whose expressions can be written as edge labels in the HOA format.
pub trait HoaSuitableAlphabet: Alphabet {
    /// Writes an expression as an edge label (without the surrounding brackets).
    fn write_expression<W: Write>(&self, w: &mut W, expr: &Self::Expression) -> std::fmt::Result;
    /// Writes the `AP` header item for the atomic propositions of the alphabet.
    fn write_alphabet_description<W: Write>(&self, w: &mut W) -> std::fmt::Result;
}

impl HoaSuitableAlphabet for CharAlphabet {
    fn write_alphabet_description<W: Write>(&self, w: &mut W) -> std::fmt::Result {
        writeln!(
            w,
            "AP: {} {}",
            self.size(),
            (0..self.size())
                .map(|i| ((b'a') + (i as u8)) as char)
                .map(|c| format!("\"{}\"", c))
                .join(" ")
        )
    }

    fn write_expression<W: Write>(&self, w: &mut W, expr: &Self::Expression) -> std::fmt::Result {
        write!(
            w,
            "{}",
            (0..self.size())
                .map(|i| if i as u8 == (*expr as u8) - (b'a') {
                    format!("{i}")
                } else {
                    format!("!{i}")
                })
                .join(" & ")
        )
    }
}

impl HoaSuitableAlphabet for PropAlphabet {
    fn write_alphabet_description<W: Write>(&self, w: &mut W) -> std::fmt::Result {
        writeln!(
            w,
            "AP: {} {}",
            self.aps(),
            self.apnames()
                .iter()
                .map(|name| format!("\"{}\"", name))
                .join(" ")
        )
    }

    fn write_expression<W: Write>(&self, w: &mut W, expr: &Self::Expression) -> std::fmt::Result {
        write!(w, "{}", expr.to_hoa_label())
    }
}

/// The parity formula over the acceptance sets in `order`, which lists them from the one that
/// decides first to the one that decides last (increasing for min, decreasing for max). A set is
/// accepting if its parity is even (`even`) or odd (`!even`).
fn build_parity_condition_hoa(order: &[Int], even: bool) -> String {
    let accepting = |set: Int| (set % 2 == 0) == even;
    match order {
        [] => "f".to_string(),
        [only] => if accepting(*only) { "t" } else { "f" }.to_string(),
        [set, last] if accepting(*set) => format!("Inf({set}) | Fin({last})"),
        [set, last] => format!("Fin({set}) & Inf({last})"),
        [set, rest @ ..] if accepting(*set) => {
            format!("Inf({set}) | ({})", build_parity_condition_hoa(rest, even))
        }
        [set, rest @ ..] => {
            format!("Fin({set}) & ({})", build_parity_condition_hoa(rest, even))
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn written_hoa_uses_proposition_indices_and_round_trips() {
        use crate::hoa::HoaString;

        let input = r#"HOA: v1
States: 2
Start: 0
acc-name: parity min even 3
Acceptance: 3 Inf(0) | (Fin(1) & Inf(2))
AP: 2 "a" "b"
--BODY--
State: 0
[0 & !1] 1 {1}
[!0 & 1] 0 {0}
[!0 & !1] 0 {2}
[0 & 1] 1 {2}
State: 1
[0] 0 {1}
[!0] 1 {2}
--END--
"#;
        let parse = |text: &str| {
            HoaString::from(text.to_string())
                .pop::<crate::ts::Det<crate::ts::Linked>>()
                .expect("valid HOA")
                .into_dpa()
                .expect("a parity automaton")
        };
        let first = parse(input).to_hoa().unwrap();
        for label in first
            .lines()
            .filter(|line| line.starts_with('['))
            .map(|line| &line[1..line.find(']').unwrap()])
        {
            assert!(
                label
                    .chars()
                    .all(|c| c.is_ascii_digit() || " !&|()".contains(c)),
                "labels must be written over proposition indices: {label}"
            );
        }
        let second = parse(&first).to_hoa().unwrap();
        // the edges of a state are written newest first, so their order flips with every parse
        let per_state = |text: &str| {
            let mut states: Vec<Vec<String>> = Vec::new();
            for line in text.lines() {
                if line.starts_with("State:") {
                    states.push(Vec::new());
                }
                if let Some(state) = states.last_mut() {
                    state.push(line.to_string());
                }
            }
            states.iter_mut().for_each(|lines| lines.sort());
            states
        };
        assert_eq!(per_state(&first), per_state(&second));
    }

    #[test]
    fn omega_acceptance_conditions_are_written() {
        use crate::automaton::{OmegaAcceptanceCondition::*, ParityKind, RabinPair};
        let header_with = |mask: &[crate::Int], acc| {
            let aut = Builder::default()
                .with_state_colors([crate::Void])
                .with_edges([(
                    0,
                    'a',
                    crate::automaton::AcceptanceMask::from_iter(mask.iter().copied()),
                    0,
                )])
                .into_automaton(0, acc);
            let hoa = super::WriteHoa::to_hoa(&aut).expect("writable");
            let acceptance = hoa.lines().skip(4).take_while(|l| *l != "--BODY--");
            acceptance.collect::<Vec<_>>().join("\n")
        };
        let header = |acc| header_with(&[0, 2], acc);
        assert_eq!(header(Buchi), "acc-name: Buchi\nAcceptance: 1 Inf(0)");
        assert_eq!(header(CoBuchi), "acc-name: co-Buchi\nAcceptance: 1 Fin(0)");
        assert_eq!(
            header(Parity(ParityKind::MaxEven, 0, 2)),
            "acc-name: parity max even 3\nAcceptance: 3 Inf(2) | (Fin(1) & Inf(0))"
        );
        assert_eq!(
            header(Parity(ParityKind::MinOdd, 0, 2)),
            "acc-name: parity min odd 3\nAcceptance: 3 Fin(0) & (Inf(1) | Fin(2))"
        );
        assert_eq!(
            header(Parity(ParityKind::MaxOdd, 0, 2)),
            "acc-name: parity max odd 3\nAcceptance: 3 Fin(2) & (Inf(1) | Fin(0))"
        );
        assert_eq!(
            header(Rabin(vec![RabinPair::from_iters([0], [1, 2])])),
            "Acceptance: 3 (Fin(0)) & (Inf(1) | Inf(2))"
        );
        assert_eq!(
            header(Streett(vec![
                RabinPair::from_iters([0], [1]),
                RabinPair::from_iters([], [2])
            ])),
            "Acceptance: 3 (Fin(0)) | (Inf(1)) & (t) | (Inf(2))"
        );
        assert_eq!(
            header_with(&[], Rabin(vec![])),
            "acc-name: Rabin 0\nAcceptance: 0 f"
        );
        assert_eq!(
            header_with(&[], Streett(vec![])),
            "acc-name: Streett 0\nAcceptance: 0 t"
        );
        // the sets of the edges have to exist, and then the pairs are not the standard ones
        assert_eq!(header(Rabin(vec![])), "Acceptance: 3 f");
    }

    #[test]
    fn parsed_omega_automata_are_written_unchanged() {
        use crate::hoa::HoaString;
        let input = "HOA: v1\nAP: 1 \"a\"\nStates: 2\nStart: 0\nacc-name: parity min even 3\nAcceptance: 3 Inf(0) | (Fin(1) & Inf(2))\n--BODY--\nState: 0\n[0] 1 {1}\n[!0] 0 {0}\nState: 1\n[0] 0 {2}\n[!0] 1 {1}\n--END--\n";
        let aut = HoaString::from(input.to_string())
            .pop::<crate::ts::Det<crate::ts::Linked>>()
            .expect("valid HOA");
        let sorted = |hoa: &str| {
            let mut lines: Vec<_> = hoa.lines().map(str::to_string).collect();
            lines.sort();
            lines
        };
        // the order of the edges of a state is not part of the comparison
        let written = super::WriteHoa::to_hoa(&aut).unwrap();
        assert_eq!(sorted(&written), sorted(input));
    }

    #[test]
    fn edge_colors_of_omega_automata_list_their_sets() {
        use crate::automaton::{AcceptanceMask, OmegaAcceptanceCondition::Buchi};
        let aut = Builder::default()
            .with_state_colors([crate::Void])
            .with_edges([
                (0, 'a', AcceptanceMask::from_iter([0, 2]), 0),
                (0, 'b', AcceptanceMask::from_iter([]), 0),
            ])
            .into_automaton(0, Buchi);
        let hoa = super::WriteHoa::to_hoa(&aut).expect("writable");
        assert!(hoa.contains("[0 & !1] 0 {0 2}\n"), "{hoa}");
        assert!(hoa.contains("[!0 & 1] 0\n--END--"), "{hoa}");
    }

    use super::WriteHoa;
    use crate::ts::Builder;

    #[test]
    fn build_parity_hoa_string() {
        assert_eq!(
            crate::hoa::output::build_parity_condition_hoa(&[0, 1, 2, 3, 4], true),
            "Inf(0) | (Fin(1) & (Inf(2) | (Fin(3) & Inf(4))))"
        );
        assert_eq!(
            crate::hoa::output::build_parity_condition_hoa(&[0, 1, 2], true),
            "Inf(0) | (Fin(1) & Inf(2))"
        );
    }

    #[test]
    fn write_hoa_dpa() {
        let dpa = Builder::without_state_colors()
            .with_edges([(0, 'a', 0, 0), (0, 'b', 1, 0), (0, 'c', 2, 0)])
            .into_dpa(0);
        let hoa = dpa.to_hoa().unwrap();
        assert_eq!(
            hoa,
            "HOA: v1\nAP: 3 \"a\" \"b\" \"c\"\nStates: 1\nStart: 0\nacc-name: parity min even 3\nAcceptance: 3 Inf(0) | (Fin(1) & Inf(2))\n--BODY--\nState: 0\n[0 & !1 & !2] 0 {0}\n[!0 & 1 & !2] 0 {1}\n[!0 & !1 & 2] 0 {2}\n--END--\n"
        );
    }

    #[test]
    fn parity_sets_start_at_zero_even_if_unused() {
        let dpa = Builder::without_state_colors()
            .with_edges([(0, 'a', 2, 0), (0, 'b', 3, 0)])
            .into_dpa(0);
        let hoa = dpa.to_hoa().unwrap();
        assert!(hoa.contains("Acceptance: 4 "), "{hoa}");
        assert!(hoa.contains("{2}\n") && hoa.contains("{3}\n"), "{hoa}");
    }

    #[test]
    fn typed_conditions_are_written_and_read_back() {
        use crate::automaton::{
            Existential, MaxEvenParityCondition, MaxOddParityCondition, MinEvenParityCondition,
            MinOddParityCondition, OmegaAcceptanceCondition, ParityKind, RabinCondition, RabinPair,
        };
        use crate::hoa::HoaString;
        use crate::ts::{Det, Linked};
        let read = |hoa: String| {
            HoaString::from(hoa.clone())
                .pop::<Det<Linked>>()
                .unwrap_or_else(|| panic!("unreadable HOA\n{hoa}"))
        };
        let dpa = Builder::without_state_colors()
            .with_edges([(0, 'a', 1, 0), (0, 'b', 3, 0)])
            .into_dpa(0);
        let parity = |hoa: String, kind| {
            let acceptance = read(hoa).acceptance().clone();
            assert_eq!(acceptance, OmegaAcceptanceCondition::Parity(kind, 0, 3));
        };
        parity(dpa.to_hoa().unwrap(), ParityKind::MinEven);
        parity(
            dpa.clone()
                .map_acceptance(|_: MinEvenParityCondition| MaxEvenParityCondition)
                .to_hoa()
                .unwrap(),
            ParityKind::MaxEven,
        );
        parity(
            dpa.clone()
                .map_acceptance(|_: MinEvenParityCondition| MinOddParityCondition)
                .to_hoa()
                .unwrap(),
            ParityKind::MinOdd,
        );
        parity(
            dpa.map_acceptance(|_: MinEvenParityCondition| MaxOddParityCondition)
                .to_hoa()
                .unwrap(),
            ParityKind::MaxOdd,
        );

        // an NCW is written like a DCW
        let ncw = Builder::without_state_colors()
            .with_transitions([(0, 'a', true, 0), (0, 'a', false, 0), (0, 'b', false, 0)])
            .into_ncw(0);
        let hoa = ncw.to_hoa().unwrap();
        assert!(
            hoa.contains("acc-name: co-Buchi\nAcceptance: 1 Fin(0)\n"),
            "{hoa}"
        );
        assert!(hoa.contains(" {0}\n"), "{hoa}");

        let pair = RabinPair::from_iters([0], [1]);
        let edges = [(0, 'a', 0u8, 0), (0, 'b', 1, 0)];
        let dra = Builder::without_state_colors()
            .with_edges(edges)
            .into_automaton(0, RabinCondition::from([pair.clone()]));
        let nra = Builder::without_state_colors()
            .with_edges(edges)
            .into_nondeterministic_automaton(0, Existential(RabinCondition::from([pair.clone()])));
        for hoa in [dra.to_hoa().unwrap(), nra.to_hoa().unwrap()] {
            assert!(hoa.contains("acc-name: Rabin 1\nAcceptance: 2 "), "{hoa}");
            assert_eq!(
                *read(hoa).acceptance(),
                OmegaAcceptanceCondition::Rabin(vec![pair.clone()])
            );
        }
        // edge colors above the pairs are declared as acceptance sets
        let wide = Builder::without_state_colors()
            .with_edges([(0, 'a', 0u8, 0), (0, 'b', 4, 0)])
            .into_automaton(0, RabinCondition::from([pair.clone()]));
        let hoa = wide.to_hoa().unwrap();
        assert!(hoa.contains("\nAcceptance: 5 "), "{hoa}");
        assert!(!hoa.contains("acc-name"), "{hoa}");
    }

    #[test]
    fn write_hoa_dba() {
        let dba = Builder::without_state_colors()
            .with_edges([(0, 'a', true, 0), (0, 'b', false, 0), (0, 'c', true, 0)])
            .into_dba(0);
        let hoa = dba.to_hoa().unwrap();
        assert_eq!(
            hoa,
            "HOA: v1\nAP: 3 \"a\" \"b\" \"c\"\nStates: 1\nStart: 0\nacc-name: Buchi\nAcceptance: 1 Inf(0)\n--BODY--\nState: 0\n[0 & !1 & !2] 0 {0}\n[!0 & 1 & !2] 0\n[!0 & !1 & 2] 0 {0}\n--END--\n"
        );
    }
}
