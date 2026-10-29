use crate::DTS;
use crate::Void;
use crate::ts::States;
use itertools::Itertools;
use tracing::trace;

use std::fmt::{Result, Write};

use super::HoaError;
use crate::{
    Int, Pointed, TransitionSystem,
    alphabet::{Alphabet, CharAlphabet, PropAlphabet},
    automaton::{DBA, DPA, OmegaAcceptanceCondition},
    ts::{EdgeColor, EdgeExpression, IsEdge},
};

/// Automata that can be written in the [HOA format](https://adl.github.io/hoaf/).
pub trait WriteHoa: States + Pointed {
    /// Writes the automaton in the HOA format to the given writer.
    fn write_hoa<W: Write>(&self, w: &mut W) -> Result {
        w.write_str("HOA: v1\n")?;

        self.write_alphabet_description(w)?;

        w.write_fmt(format_args!("States: {}\n", self.state_count()))?;

        w.write_str("Start: ")?;
        self.write_state_id(w, self.initial())?;
        w.write_char('\n')?;

        self.write_acceptance(w)?;

        w.write_str("--BODY--")?;

        for state in self.states() {
            w.write_str("\nState: ")?;
            self.write_state_id(w, state)?;
            for edge in self.edges_from(state).expect("We know this state exists") {
                w.write_char('\n')?;
                w.write_char('[')?;
                self.write_expression(w, edge.expression())?;
                w.write_char(']')?;
                w.write_char(' ')?;

                self.write_state_id(w, edge.target())?;

                w.write_char(' ')?;
                self.write_edge_color(w, edge.color().into_owned())?;
            }
        }

        w.write_str("\n--END--\n")?;

        Ok(())
    }

    /// Writes the color of an edge, i.e. the acceptance sets it belongs to.
    fn write_edge_color<W: std::fmt::Write>(&self, w: &mut W, label: EdgeColor<Self>) -> Result;

    /// Writes the label of an edge.
    fn write_expression<W: std::fmt::Write>(
        &self,
        w: &mut W,
        expr: &EdgeExpression<Self>,
    ) -> Result;

    /// Writes the identifier of a state.
    fn write_state_id<W: std::fmt::Write>(
        &self,
        w: &mut W,
        id: Self::StateIndex,
    ) -> std::fmt::Result;

    /// Writes the `AP` header item describing the atomic propositions.
    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result;

    /// Writes the acceptance condition (the `acc-name` and `Acceptance` header items).
    fn write_acceptance<W: std::fmt::Write>(&self, w: &mut W) -> Result;

    /// Returns the automaton in the HOA format as a string.
    fn to_hoa(&self) -> String {
        let mut w = String::new();
        self.write_hoa(&mut w)
            .expect("writing to a String cannot fail");
        trace!("produced HOA string from automaton\n{}", w);
        w
    }
}

fn write_buchi_hoa<W: Write>(w: &mut W) -> Result {
    write!(w, "acc-name: Buchi\nAcceptance: 1 Inf(0)\n")
}

fn write_parity_hoa<W: Write>(w: &mut W, low: Int, high: Int) -> Result {
    let zero_based_range = high - low + (low % 2);
    write!(
        w,
        "acc-name: parity min even {}\nAcceptance: {} {}\n",
        zero_based_range + 1,
        zero_based_range + 1,
        build_parity_condition_hoa(low, high)
    )
}

impl OmegaAcceptanceCondition {
    /// Writes the `acc-name` and `Acceptance` header items of this condition in the HOA format.
    ///
    /// # Errors
    /// Only Büchi and parity conditions can be written so far, for all others
    /// [`HoaError::UnsupportedAcceptance`] is returned. A failing writer yields
    /// [`HoaError::Format`].
    pub fn write_hoa<W: Write>(&self, w: &mut W) -> std::result::Result<(), HoaError> {
        match self {
            OmegaAcceptanceCondition::Parity(low, high) => Ok(write_parity_hoa(w, *low, *high)?),
            OmegaAcceptanceCondition::Buchi => Ok(write_buchi_hoa(w)?),
            other => Err(HoaError::UnsupportedAcceptance(format!("{other:?}"))),
        }
    }
}

/// Alphabets whose expressions can be written as edge labels in the HOA format.
pub trait HoaSuitableAlphabet: Alphabet {
    /// Writes an expression as an edge label (without the surrounding brackets).
    fn write_expression<W: std::fmt::Write>(&self, w: &mut W, expr: &Self::Expression) -> Result;
    /// Writes the `AP` header item for the atomic propositions of the alphabet.
    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result;
}

impl<A: HoaSuitableAlphabet> WriteHoa for DBA<DTS<A, Void, bool>> {
    fn write_edge_color<W: std::fmt::Write>(&self, w: &mut W, label: EdgeColor<Self>) -> Result {
        if label {
            write!(w, "{{{}}}", 0)
        } else {
            write!(w, "{{{}}}", 1)
        }
    }

    fn write_expression<W: std::fmt::Write>(
        &self,
        w: &mut W,
        expr: &EdgeExpression<Self>,
    ) -> Result {
        self.alphabet().write_expression(w, expr)
    }

    fn write_state_id<W: std::fmt::Write>(
        &self,
        w: &mut W,
        id: Self::StateIndex,
    ) -> std::fmt::Result {
        write!(w, "{}", id)
    }

    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        self.alphabet().write_alphabet_description(w)
    }

    fn write_acceptance<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        write_buchi_hoa(w)
    }
}

impl<A: HoaSuitableAlphabet> WriteHoa for DPA<DTS<A, Void, Int>> {
    fn write_edge_color<W: std::fmt::Write>(&self, w: &mut W, label: EdgeColor<Self>) -> Result {
        write!(w, "{{{}}}", label)
    }

    fn write_expression<W: std::fmt::Write>(
        &self,
        w: &mut W,
        expr: &EdgeExpression<Self>,
    ) -> Result {
        self.alphabet().write_expression(w, expr)
    }

    fn write_state_id<W: std::fmt::Write>(
        &self,
        w: &mut W,
        id: Self::StateIndex,
    ) -> std::fmt::Result {
        write!(w, "{}", id)
    }

    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        self.alphabet().write_alphabet_description(w)
    }

    fn write_acceptance<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        let (low, high) = self.low_and_high_priority();

        write_parity_hoa(w, low, high)
    }
}

impl HoaSuitableAlphabet for CharAlphabet {
    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result {
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

    fn write_expression<W: std::fmt::Write>(&self, w: &mut W, expr: &Self::Expression) -> Result {
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
    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result {
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

    fn write_expression<W: std::fmt::Write>(&self, w: &mut W, expr: &Self::Expression) -> Result {
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
                .pop::<true>()
                .expect("valid HOA")
                .into_dpa()
                .expect("a parity automaton")
        };
        let first = parse(input).to_hoa();
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
        let second = parse(&first).to_hoa();
        assert_eq!(first, second);
    }

    #[test]
    fn only_buchi_and_parity_can_be_written() {
        use crate::automaton::OmegaAcceptanceCondition;
        use crate::hoa::HoaError;

        let mut out = String::new();
        assert!(OmegaAcceptanceCondition::Buchi.write_hoa(&mut out).is_ok());
        assert!(
            OmegaAcceptanceCondition::Parity(0, 2)
                .write_hoa(&mut out)
                .is_ok()
        );
        for unsupported in [
            OmegaAcceptanceCondition::CoBuchi,
            OmegaAcceptanceCondition::Rabin,
            OmegaAcceptanceCondition::Streett,
            OmegaAcceptanceCondition::Reachability,
            OmegaAcceptanceCondition::Safety,
        ] {
            assert!(matches!(
                unsupported.write_hoa(&mut String::new()),
                Err(HoaError::UnsupportedAcceptance(_))
            ));
        }
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
        let hoa = dpa.to_hoa();
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
        let hoa = dba.to_hoa();
        assert_eq!(
            hoa,
            "HOA: v1\nAP: 3 \"a\" \"b\" \"c\"\nStates: 1\nStart: 0\nacc-name: Buchi\nAcceptance: 1 Inf(0)\n--BODY--\nState: 0\n[0 & !1 & !2] 0 {0}\n[!0 & 1 & !2] 0 {1}\n[!0 & !1 & 2] 0 {0}\n--END--\n"
        );
    }
}
