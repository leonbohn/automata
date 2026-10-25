//! Reading and writing automata in the [HOA format](https://adl.github.io/hoaf/), using the
//! [`hoars`](https://github.com/leonbohn/hoars) crate. Only available with the feature `hoa`.
//!
//! Deterministic Büchi and parity automata can be parsed from a [`HoaString`] and written back
//! with [`WriteHoa::to_hoa`]. Edges of parsed automata are labeled by formulas over the atomic
//! propositions (a [`PropAlphabet`]).
//!
//! ```
//! use automata::{TransitionSystem, hoa::{HoaString, WriteHoa}};
//!
//! let text = r#"HOA: v1
//! States: 2
//! Start: 0
//! acc-name: parity min even 3
//! Acceptance: 3 Inf(0) | (Fin(1) & Inf(2))
//! AP: 2 "a" "b"
//! --BODY--
//! State: 0
//! [0 & !1] 1 {1}
//! [!0 & 1] 0 {0}
//! State: 1
//! [0 & !1] 0 {1}
//! [!0 & 1] 1 {2}
//! --END--
//! "#;
//!
//! // a string may contain several automata, `pop` removes the first one
//! let mut hoa = HoaString::from(text.to_string());
//! let automaton = hoa.pop::<true>().expect("a valid deterministic automaton");
//! assert_eq!(automaton.size(), 2);
//!
//! // convert to a deterministic parity automaton and write it back
//! let dpa = automaton.into_dpa().expect("a parity automaton");
//! let written = dpa.to_hoa();
//! assert!(written.contains("acc-name: parity min even 3"));
//! assert!(written.contains("[0 & !1] 1 {1}"));
//! ```
//!
//! Only deterministic Büchi and parity automata are supported so far. Reading fails with a
//! [`HoaError`] for other acceptance conditions, alternating automata and unsupported inputs.

use tracing::{trace, warn};

mod error;
pub use error::HoaError;

/// Reading automata from a stream or a string.
pub mod input;
pub use input::{
    HoaAutomatonStream, IntoDeterministicHoaAutomatonStream, NondeterministicHoaAutomatonStream,
};

/// Writing automata in the HOA format.
pub mod output;
pub use output::WriteHoa;

pub use hoars::*;

use crate::alphabet::PropAlphabet;

/// An omega automaton over a propositional alphabet, as it is obtained from the HOA format. The
/// constant `DET` indicates whether it is known to be deterministic.
pub type HoaAutomaton<const DET: bool> = crate::automaton::OmegaAutomaton<PropAlphabet, DET>;

/// A string that contains HOA automata, one after the other.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct HoaString(pub(crate) String);

impl HoaString {
    /// Returns the underlying string.
    pub fn into_inner(self) -> String {
        self.0
    }

    /// Removes the first valid automaton from the string and returns it. Parts of the string that
    /// cannot be parsed as an automaton (or are not deterministic, if `DET` is true) are skipped.
    pub fn pop<const DET: bool>(&mut self) -> Option<HoaAutomaton<DET>> {
        const END_LEN: usize = "--END--".len();
        const ABORT_LEN: usize = "--ABORT--".len();

        loop {
            // the part of the string that holds the next automaton, if there is one
            let (start, end) = match (self.0.find("--ABORT--"), self.0.find("--END--")) {
                (Some(abort), Some(end)) if abort < end => {
                    trace!("Found --ABORT-- before --END--, taking the automaton from {abort}");
                    (abort + ABORT_LEN, end + END_LEN)
                }
                (_, Some(end)) => {
                    trace!("Found --END--, taking the first automaton up to {end}");
                    (0, end + END_LEN)
                }
                (Some(abort), None) => {
                    trace!("Found only the --ABORT--ed automaton at {abort} without an --END--");
                    return None;
                }
                (None, None) => {
                    trace!("No end of automaton found, there is no automaton to parse.");
                    return None;
                }
            };

            let parsed = input::parse_omega_automaton_range(&self.0, start, end);
            self.0 = self.0[end..].trim_start().to_string();
            match parsed {
                Ok(automaton) => return Some(automaton),
                Err(error) => warn!("Could not parse automaton, skipping... {:?}", error),
            }
        }
    }
}

impl std::ops::Deref for HoaString {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for HoaString {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl std::borrow::Borrow<str> for HoaString {
    fn borrow(&self) -> &str {
        self.0.as_str()
    }
}
impl From<String> for HoaString {
    fn from(value: String) -> Self {
        Self(value)
    }
}
impl From<HoaString> for String {
    fn from(value: HoaString) -> Self {
        value.0
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn pop_removes_the_automata_one_after_the_other() {
        use crate::hoa::HoaString;

        let one = "HOA: v1\nStates: 1\nStart: 0\nacc-name: Buchi\nAcceptance: 1 Inf(0)\nAP: 1 \"a\"\n--BODY--\nState: 0\n[t] 0 {0}\n--END--\n";
        let two = "HOA: v1\nStates: 2\nStart: 0\nacc-name: Buchi\nAcceptance: 1 Inf(0)\nAP: 1 \"a\"\n--BODY--\nState: 0\n[0] 1\n[!0] 0\nState: 1\n[t] 1 {0}\n--END--\n";
        // the segment in the middle ends with `--END--`, but uses an unsupported acceptance condition
        let invalid = "HOA: v1\nStates: 1\nStart: 0\nacc-name: Rabin 1\nAcceptance: 2 Fin(0) & Inf(1)\nAP: 1 \"a\"\n--BODY--\nState: 0\n[t] 0 {0}\n--END--\n";
        let mut hoa = HoaString::from(format!("{one}{invalid}{two}"));

        assert_eq!(hoa.pop::<true>().map(|a| a.size()), Some(1));
        assert_eq!(hoa.pop::<true>().map(|a| a.size()), Some(2));
        assert!(hoa.pop::<true>().is_none());
        assert!(hoa.is_empty());
    }

    use crate::{TransitionSystem, hoa::input::hoa_to_ts};

    #[test]
    fn parse_generated_hoa() {
        let hoa = r#"HOA: v1
        States: 10
        Start: 0
        AP: 3 "2" "a" "b"
        acc-name: parity min even 5
        Acceptance: 5 Inf(0) | (Fin(1) & (Inf(2) | (Fin(3) & Inf(4))))
        properties: trans-labels explicit-labels trans-acc complete
        properties: deterministic
        --BODY--
        State: 0
        [0&1] 4
        [0&!1] 8
        [!0] 6 {0}
        State: 1
        [!0&1&2] 7 {0}
        [!0&1&!2] 3 {4}
        [!0&!1&2] 4 {0 4}
        [!0&!1&!2] 9 {0}
        [0] 5 {0 4}
        State: 2
        [0&1&2] 2 {0 4}
        [0&1&!2] 6 {3}
        [0&!1&2] 1 {1}
        [0&!1&!2] 4 {1}
        [!0] 7
        State: 3
        [0&1] 0 {2}
        [0&!1] 2
        [!0&1] 4 {3 4}
        [!0&!1] 6 {1 2}
        State: 4
        [0&1] 0 {3}
        [0&!1] 6 {1}
        [!0&1] 7 {0}
        [!0&!1] 4
        State: 5
        [0&1] 9
        [0&!1] 2
        [!0] 4
        State: 6
        [0&1] 9 {4}
        [0&!1] 0 {2}
        [!0&1] 6 {2 3}
        [!0&!1] 4 {0}
        State: 7
        [0&!1&2] 8 {4}
        [0&!1&!2] 1 {4}
        [0&1] 2 {1}
        [!0] 4 {2}
        State: 8
        [!0&1] 2
        [!0&!1] 6
        [0] 4
        State: 9
        [0] 5
        [!0] 3
        --END--
        "#;
        let auts = hoa_to_ts(hoa);
        assert_eq!(auts.len(), 1);
        let aut = &auts[0];
        assert_eq!(aut.size(), 10);
    }
}
