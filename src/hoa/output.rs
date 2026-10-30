use crate::automaton::{
    AcceptanceMask, Automaton, BuchiCondition, MinEvenParityCondition, OmegaAcceptanceCondition,
    RabinPair,
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

    /// Writes the acceptance sets that an edge with the given color belongs to, including the
    /// surrounding braces. Nothing is written if the edge belongs to no set.
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
            for edge in ts.edges_from(state).expect("We know this state exists") {
                w.write_str("\n[")?;
                ts.alphabet().write_expression(w, edge.expression())?;
                write!(w, "] {} ", edge.target().into_usize())?;
                self.acceptance().write_edge_color(edge.color(), w)?;
            }
        }
        w.write_str("\n--END--\n")?;
        Ok(())
    }
}

impl<T: States<EdgeColor = bool>> HoaAcceptance<T> for BuchiCondition {
    fn write_acceptance<W: Write>(&self, _ts: &T, w: &mut W) -> Result<(), HoaError> {
        Ok(write_buchi_hoa(w)?)
    }

    fn write_edge_color<W: Write>(&self, color: &bool, w: &mut W) -> Result<(), HoaError> {
        Ok(write!(w, "{{{}}}", if *color { 0 } else { 1 })?)
    }
}

impl<T: States<EdgeColor = Int>> HoaAcceptance<T> for MinEvenParityCondition {
    fn write_acceptance<W: Write>(&self, ts: &T, w: &mut W) -> Result<(), HoaError> {
        let mut colors = ts
            .states()
            .flat_map(|q| ts.edges_from(q).into_iter().flatten())
            .map(|edge| *edge.color());
        let first = colors.next().unwrap_or(0);
        let (low, high) = colors.fold((first, first), |(l, h), c| (l.min(c), h.max(c)));
        Ok(write_parity_hoa(w, low, high)?)
    }

    fn write_edge_color<W: Write>(&self, color: &Int, w: &mut W) -> Result<(), HoaError> {
        Ok(write!(w, "{{{color}}}")?)
    }
}

impl<T: States<EdgeColor = AcceptanceMask>> HoaAcceptance<T> for OmegaAcceptanceCondition {
    fn write_acceptance<W: Write>(&self, _ts: &T, w: &mut W) -> Result<(), HoaError> {
        match self {
            OmegaAcceptanceCondition::Parity(low, high) => Ok(write_parity_hoa(w, *low, *high)?),
            OmegaAcceptanceCondition::MaxParity(_, high) => Ok(write_max_parity_hoa(w, *high)?),
            OmegaAcceptanceCondition::Buchi | OmegaAcceptanceCondition::Reachability => {
                Ok(write_buchi_hoa(w)?)
            }
            OmegaAcceptanceCondition::CoBuchi | OmegaAcceptanceCondition::Safety => {
                Ok(write!(w, "acc-name: co-Buchi\nAcceptance: 1 Fin(0)\n")?)
            }
            OmegaAcceptanceCondition::Rabin(pairs) => {
                Ok(write_pairs_hoa(w, pairs, " | ", "f", " & ")?)
            }
            OmegaAcceptanceCondition::Streett(pairs) => {
                Ok(write_pairs_hoa(w, pairs, " & ", "t", " | ")?)
            }
        }
    }

    fn write_edge_color<W: Write>(&self, mask: &AcceptanceMask, w: &mut W) -> Result<(), HoaError> {
        if mask.iter().next().is_some() {
            write!(w, "{{{}}}", mask.iter().join(" "))?;
        }
        Ok(())
    }
}

fn write_buchi_hoa<W: Write>(w: &mut W) -> std::fmt::Result {
    write!(w, "acc-name: Buchi\nAcceptance: 1 Inf(0)\n")
}

fn write_parity_hoa<W: Write>(w: &mut W, low: Int, high: Int) -> std::fmt::Result {
    let zero_based_range = high - low + (low % 2);
    write!(
        w,
        "acc-name: parity min even {}\nAcceptance: {} {}\n",
        zero_based_range + 1,
        zero_based_range + 1,
        build_parity_condition_hoa(low, high)
    )
}

/// Writes a max parity condition over the acceptance sets `0..=high` in which the largest set
/// seen infinitely often is accepting if it has the same parity as `high`.
fn write_max_parity_hoa<W: Write>(w: &mut W, high: Int) -> std::fmt::Result {
    let accepting_parity = high % 2;
    let mut formula = if accepting_parity == 0 { "Inf(0)" } else { "f" }.to_string();
    for set in 1..=high {
        formula = if set % 2 == accepting_parity {
            format!("Inf({set}) | ({formula})")
        } else {
            format!("Fin({set}) & ({formula})")
        };
    }
    write!(
        w,
        "acc-name: parity max {} {}\nAcceptance: {} {formula}\n",
        if accepting_parity == 0 { "even" } else { "odd" },
        high + 1,
        high + 1,
    )
}

/// Writes a Rabin or Streett condition. A pair is `Fin(..) <pair_op> Inf(..)`, the pairs are
/// joined by `pair_join`, `empty` is the condition without pairs.
fn write_pairs_hoa<W: Write>(
    w: &mut W,
    pairs: &[RabinPair<Int>],
    pair_join: &str,
    empty: &str,
    pair_op: &str,
) -> std::fmt::Result {
    let sets = pairs
        .iter()
        .flat_map(|p| p.fin.iter().chain(&p.inf))
        .max()
        .map_or(0, |m| m + 1);
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

/// Assumes that `low` is the least occurring and `high` is the highest occurring priority,
/// *inclusive*.
fn build_parity_condition_hoa(low: Int, high: Int) -> String {
    let parity = low % 2;

    let even = parity == 0;

    if high <= low {
        return if even { "t" } else { "f" }.to_string();
    }

    match high - low {
        0 => {
            if even {
                format!("Inf({low})")
            } else {
                format!("Fin({low})")
            }
        }
        1 => {
            if even {
                format!("Inf({low}) | Fin({high})")
            } else {
                format!("Fin({low}) & Inf({high})")
            }
        }
        _ => {
            let rest = build_parity_condition_hoa(low + 1, high);
            if even {
                format!("Inf({low}) | ({rest})")
            } else {
                format!("Fin({low}) & ({rest})")
            }
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
        assert_eq!(first, second);
    }

    #[test]
    fn omega_acceptance_conditions_are_written() {
        use crate::automaton::{OmegaAcceptanceCondition::*, RabinPair};
        let header = |acc| {
            let aut = Builder::default()
                .with_state_colors([crate::Void])
                .with_edges([(
                    0,
                    'a',
                    crate::automaton::AcceptanceMask::from_iter([0, 2]),
                    0,
                )])
                .into_automaton(0, acc);
            let hoa = super::WriteHoa::to_hoa(&aut).expect("writable");
            let acceptance = hoa.lines().skip(4).take_while(|l| *l != "--BODY--");
            acceptance.collect::<Vec<_>>().join("\n")
        };
        assert_eq!(header(Buchi), "acc-name: Buchi\nAcceptance: 1 Inf(0)");
        assert_eq!(header(CoBuchi), "acc-name: co-Buchi\nAcceptance: 1 Fin(0)");
        assert_eq!(
            header(MaxParity(0, 2)),
            "acc-name: parity max even 3\nAcceptance: 3 Inf(2) | (Fin(1) & (Inf(0)))"
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
        assert_eq!(header(Rabin(vec![])), "Acceptance: 0 f");
        assert_eq!(header(Streett(vec![])), "Acceptance: 0 t");
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
        assert!(hoa.contains("[!0 & 1] 0 \n--END--"), "{hoa}");
    }

    use super::WriteHoa;
    use crate::ts::Builder;

    #[test]
    fn build_parity_hoa_string() {
        assert_eq!(
            crate::hoa::output::build_parity_condition_hoa(0, 4),
            "Inf(0) | (Fin(1) & (Inf(2) | (Fin(3) & Inf(4))))"
        );
        assert_eq!(
            crate::hoa::output::build_parity_condition_hoa(0, 2),
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
    fn write_hoa_dba() {
        let dba = Builder::without_state_colors()
            .with_edges([(0, 'a', true, 0), (0, 'b', false, 0), (0, 'c', true, 0)])
            .into_dba(0);
        let hoa = dba.to_hoa().unwrap();
        assert_eq!(
            hoa,
            "HOA: v1\nAP: 3 \"a\" \"b\" \"c\"\nStates: 1\nStart: 0\nacc-name: Buchi\nAcceptance: 1 Inf(0)\n--BODY--\nState: 0\n[0 & !1 & !2] 0 {0}\n[!0 & 1 & !2] 0 {1}\n[!0 & !1 & 2] 0 {0}\n--END--\n"
        );
    }
}
