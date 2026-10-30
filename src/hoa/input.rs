use std::{io::BufRead, ops::Deref};

use crate::automaton::{
    AcceptanceMask, DeterministicOmegaAutomaton, OmegaAcceptanceCondition, OmegaAutomaton,
};
use crate::ts::{Det, ForAlphabet, Linked, LinkedTs, Sproutable, Storage};
use crate::{
    Int,
    alphabet::{PropAlphabet, PropAlphabetError, PropExpression},
};
use hoars::HoaRepresentation;
use tracing::{trace, warn};

use super::{HoaError, HoaString};

/// Reads HOA automata from a stream and yields the deterministic ones, nondeterministic and
/// invalid automata are skipped with a warning.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct IntoDeterministicHoaAutomatonStream<R> {
    base: HoaAutomatonStream<R, Linked>,
}

impl<R> IntoDeterministicHoaAutomatonStream<R> {
    /// Creates a new stream from the given reader.
    pub fn new(read: R) -> IntoDeterministicHoaAutomatonStream<R> {
        Self {
            base: HoaAutomatonStream::new(read),
        }
    }
}

impl<R: BufRead> Iterator for IntoDeterministicHoaAutomatonStream<R> {
    type Item = DeterministicOmegaAutomaton<PropAlphabet>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            {
                let aut = self.base.next()?;
                if let Ok(det) = aut.try_into_deterministic() {
                    return Some(det);
                } else {
                    warn!("Encountered automaton that is not deterministic, skipping...")
                }
            }
        }
    }
}

/// A stream of HOA automata that are not necessarily deterministic.
pub type NondeterministicHoaAutomatonStream<R> = HoaAutomatonStream<R, Linked>;

/// Reads HOA automata from a stream. The storage `S` decides the representation of the automata: for
/// [`Det<Linked>`] (the default), automata that are not deterministic are rejected.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct HoaAutomatonStream<R, S = Det<Linked>> {
    read: R,
    buf: String,
    pos: usize,
    storage: std::marker::PhantomData<fn() -> S>,
}

impl<R: BufRead, S: HoaStorage> Iterator for HoaAutomatonStream<R, S> {
    type Item = OmegaAutomaton<PropAlphabet, S>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.read.read_line(&mut self.buf) {
                Ok(0) => return None,
                Ok(read_bytes) => {
                    if self.buf[self.pos..].contains("--ABORT--") {
                        trace!("encountered --ABORT-- in stream, resetting");
                        self.buf.clear();
                        self.pos = 0;
                        continue;
                    }

                    if self.buf[self.pos..].contains("--END--") {
                        let end = self.pos + "--END--".len();
                        trace!(
                            "encountered --END-- in stream, attempting to parse automaton \n{}",
                            &self.buf[..end]
                        );
                        let aut: Result<OmegaAutomaton<PropAlphabet, S>, _> =
                            parse_omega_automaton_range::<S>(&self.buf, 0, end);
                        self.buf.clear();
                        self.pos = 0;

                        match aut {
                            Err(e) => {
                                warn!(
                                    "Encountered automaton that could not be parsed, skipping... {:?}",
                                    e
                                );
                            }
                            Ok(aut) => return Some(aut),
                        }
                    }

                    self.pos += read_bytes;
                }
                Err(_e) => return None,
            }
        }
    }
}

impl<R, S> HoaAutomatonStream<R, S> {
    /// Creates a new stream from the given reader.
    pub fn new(read: R) -> Self {
        Self {
            read,
            pos: 0,
            buf: String::new(),
            storage: std::marker::PhantomData,
        }
    }
}

/// Parses the part `hoa[start..end]` of the given string as an omega automaton.
///
/// # Errors
///
/// Returns a [`HoaError`] if the part is not a valid HOA automaton, if it uses an unsupported
/// feature, or (for `DET`) if it is not deterministic. The error contains the range.
pub fn parse_omega_automaton_range<S: HoaStorage>(
    hoa: &str,
    start: usize,
    end: usize,
) -> Result<OmegaAutomaton<PropAlphabet, S>, HoaError> {
    let in_range = |source: HoaError| HoaError::InRange {
        start,
        end,
        source: Box::new(source),
    };
    let aut = HoaRepresentation::try_from(&hoa[start..end]).map_err(|e| in_range(e.into()))?;
    S::from_hoa(aut).map_err(in_range)
}

/// Removes the first valid deterministic automaton from `hoa`. Returns it together with the
/// remaining string, or `None` if there is no such automaton.
pub fn pop_deterministic_omega_automaton(
    hoa: HoaString,
) -> Option<(DeterministicOmegaAutomaton<PropAlphabet>, HoaString)> {
    pop_omega_automaton::<Det<Linked>>(hoa)
}

/// Tries to `pop` the foremost valid HOA automaton from the given [`HoaString`].
/// If no valid automaton is found before the end of the stream is reached, the
/// function returns `None`.
pub fn pop_omega_automaton<S: HoaStorage>(
    hoa: HoaString,
) -> Option<(OmegaAutomaton<PropAlphabet, S>, HoaString)> {
    let mut hoa = hoa;
    const END_LEN: usize = "--END--".len();
    const ABORT_LEN: usize = "--ABORT--".len();

    loop {
        match (hoa.0.find("--ABORT--"), hoa.0.find("--END--")) {
            (None, Some(pos)) => {
                trace!("Returnting first automaton, going up to position {pos}");
                match parse_omega_automaton_range::<S>(&hoa.0, 0, pos + END_LEN) {
                    Ok(aut) => {
                        return Some((
                            aut,
                            HoaString(hoa.0[pos + END_LEN..].trim_start().to_string()),
                        ));
                    }
                    Err(e) => {
                        warn!("Could not parse automaton, skipping... {:?}", e);
                        hoa = HoaString(hoa.0[pos + END_LEN..].trim_start().to_string());
                    }
                }
            }
            (Some(abort), None) => {
                trace!(
                    "Found only one automaton --ABORT--ed at {abort}, but no subsequent --END-- of automaton to parse."
                );
                return None;
            }
            (Some(abort), Some(end)) => {
                if abort < end {
                    trace!(
                        "Found --ABORT-- before --END--, returning first automaton from {abort} to {end}"
                    );
                    match parse_omega_automaton_range::<S>(&hoa.0, abort + ABORT_LEN, end + END_LEN)
                    {
                        Ok(aut) => {
                            return Some((
                                aut,
                                HoaString(hoa.0[end + END_LEN..].trim_start().to_string()),
                            ));
                        }
                        Err(e) => {
                            warn!("Could not parse automaton, skipping... {:?}", e);
                            hoa = HoaString(hoa.0[end + END_LEN..].trim_start().to_string());
                        }
                    }
                } else {
                    trace!("Found --END--, returning first automaton up to {end}");
                    match parse_omega_automaton_range::<S>(&hoa.0, 0, end + END_LEN) {
                        Ok(aut) => {
                            return Some((
                                aut,
                                HoaString(hoa.0[end + END_LEN..].trim_start().to_string()),
                            ));
                        }
                        Err(e) => {
                            warn!("Could not parse automaton, skipping... {:?}", e);
                            hoa = HoaString(hoa.0[end + END_LEN..].trim_start().to_string());
                        }
                    }
                }
            }
            (None, None) => {
                trace!("No end of automaton found, there is no automaton to parse.");
                return None;
            }
        }
    }
}

/// Considers the given HOA string as a single automaton and tries to parse it into an
/// [`OmegaAutomaton`].
pub fn hoa_to_ts<S: HoaStorage>(hoa: &str) -> Vec<OmegaAutomaton<PropAlphabet, S>> {
    let mut out = vec![];
    for hoa_aut in hoars::parse_hoa_automata(hoa) {
        match S::from_hoa(hoa_aut) {
            Ok(aut) => out.push(aut),
            Err(e) => tracing::warn!("Encountered parsing error {}", e),
        }
    }
    out
}

impl TryFrom<&hoars::Header> for OmegaAcceptanceCondition {
    type Error = HoaError;

    fn try_from(value: &hoars::Header) -> Result<Self, Self::Error> {
        let acceptance_sets = value.iter().find_map(|it| match it {
            hoars::HeaderItem::Acceptance(acceptance, _cond) => Some(*acceptance),
            _ => None,
        });

        match value.acceptance_name() {
            hoars::AcceptanceName::Buchi => Ok(OmegaAcceptanceCondition::Buchi),
            hoars::AcceptanceName::Parity => {
                let sets = acceptance_sets.ok_or(HoaError::MissingAcceptanceSets)?;
                Ok(OmegaAcceptanceCondition::Parity(
                    0,
                    (sets as Int).saturating_sub(1),
                ))
            }
            other => Err(HoaError::UnsupportedAcceptance(format!("{other:?}"))),
        }
    }
}

/// The storages that automata can be read into: [`Linked`] for automata that are not necessarily
/// deterministic and [`Det<Linked>`] for deterministic ones.
pub trait HoaStorage: Storage<PropAlphabet> {
    /// Converts the representation of an automaton in the HOA format into an omega automaton stored
    /// in `Self`.
    ///
    /// # Errors
    /// Returns a [`HoaError`] if the automaton uses an unsupported feature or cannot be stored in
    /// `Self` because it is not deterministic.
    fn from_hoa(aut: HoaRepresentation) -> Result<OmegaAutomaton<PropAlphabet, Self>, HoaError>
    where
        Self: Sized;
}

impl HoaStorage for Linked {
    fn from_hoa(aut: HoaRepresentation) -> Result<OmegaAutomaton<PropAlphabet, Self>, HoaError> {
        let (ts, initial, acceptance) = hoa_automaton_parts(aut)?;
        Ok(crate::Automaton::from_parts_with_acceptance(
            ts, initial, acceptance,
        ))
    }
}

impl HoaStorage for Det<Linked> {
    fn from_hoa(aut: HoaRepresentation) -> Result<OmegaAutomaton<PropAlphabet, Self>, HoaError> {
        let (ts, initial, acceptance) = hoa_automaton_parts(aut)?;
        let ts = ts.try_into_deterministic().map_err(|_| {
            warn!("rejecting nondeterministic automaton");
            HoaError::NotDeterministic
        })?;
        Ok(crate::Automaton::from_parts_with_acceptance(
            ts, initial, acceptance,
        ))
    }
}

impl TryFrom<HoaRepresentation> for OmegaAutomaton<PropAlphabet, Linked> {
    type Error = HoaError;
    fn try_from(value: HoaRepresentation) -> Result<Self, Self::Error> {
        Linked::from_hoa(value)
    }
}

impl TryFrom<HoaRepresentation> for OmegaAutomaton<PropAlphabet, Det<Linked>> {
    type Error = HoaError;
    fn try_from(value: HoaRepresentation) -> Result<Self, Self::Error> {
        <Det<Linked>>::from_hoa(value)
    }
}

/// The parts of an omega automaton: transition system, initial state and acceptance condition.
type HoaParts = (
    LinkedTs<PropAlphabet, Int, AcceptanceMask>,
    crate::ts::DefaultIdType,
    OmegaAcceptanceCondition,
);

/// Converts a [`HoaRepresentation`] into the parts of an omega automaton: a [`crate::NTS`] with the same
/// semantics, the initial state and the acceptance condition. This creates the appropriate
/// number of states and inserts transitions with the appropriate labels and colors.
fn hoa_automaton_parts(aut: HoaRepresentation) -> Result<HoaParts, HoaError> {
    let aps = aut.num_aps();
    if aps > crate::hoa::MAX_APS {
        return Err(PropAlphabetError::TooManyAtomicPropositions {
            count: aps as usize,
            max: crate::hoa::MAX_APS as usize,
        }
        .into());
    }

    let alphabet = PropAlphabet::try_from_apnames(aut.aps().iter())?;
    let mut ts: LinkedTs<PropAlphabet, Int, AcceptanceMask> = LinkedTs::for_alphabet(alphabet);

    for (position, state) in aut.body().iter().enumerate() {
        if state.id() as usize != position {
            return Err(HoaError::StateOrder {
                position,
                id: state.id(),
            });
        }
        let added = ts.add_state(state.id() as Int);
        debug_assert_eq!(added as usize, position);
    }

    for state in aut.body().iter() {
        for edge in state.edges() {
            let target = edge
                .state_conjunction()
                .get_singleton()
                .ok_or(HoaError::UnsupportedAlternation)?;
            let label = edge.label().deref().clone();

            let expr = label
                .try_into_hoa_expression(aps)
                .map_err(HoaError::InvalidLabel)?;
            let color: AcceptanceMask = edge.acceptance_signature().into();

            ts.add_edge((state.id(), PropExpression::from_bdd(expr), color, target));
        }
    }

    let start = aut.start();
    if start.len() != 1 {
        return Err(HoaError::UnsupportedStartStates(start.len()));
    }
    let initial = start[0]
        .get_singleton()
        .ok_or(HoaError::UnsupportedAlternation)?;

    let acceptance: OmegaAcceptanceCondition = aut.header().try_into()?;

    Ok((ts, initial, acceptance))
}

#[cfg(test)]
mod tests {
    use crate::States;
    use crate::ts::{Det, Linked};
    use tracing::debug;

    use crate::hoa::HoaString;

    #[test]
    fn hoa_tdba_with_abort_and_nondeterministic() {
        let raw_hoa = r#"
        HOA: v1
        States: 3
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 1
        --ABORT--
        HOA: v1
        States: 2
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 0 {0}
        [!0] 0
        State: 1
        [0] 0 {0}
        [0] 1
        [!0] 0
        --END--
        HOA: v1
        States: 1
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 0 {0}
        [!0] 0
        --END--
        "#;
        let hoa = HoaString(raw_hoa.to_string());
        debug!("SADF");

        let first = super::pop_deterministic_omega_automaton(hoa);
        assert!(first.is_some());
        let (first, hoa) = first.unwrap();
        assert_eq!(first.state_count(), 1);
        assert!(hoa.0.is_empty());
    }

    #[test]
    fn parity_without_acceptance_item_is_an_error() {
        let raw_hoa = r#"
        HOA: v1
        States: 1
        Start: 0
        acc-name: parity min even 2
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 0 {0}
        [!0] 0
        --END--
        "#;
        let parsed = hoars::HoaRepresentation::try_from(raw_hoa).expect("valid HOA syntax");
        assert_eq!(
            super::OmegaAcceptanceCondition::try_from(parsed.header()),
            Err(super::HoaError::MissingAcceptanceSets)
        );
    }

    const NONDETERMINISTIC: &str = r#"HOA: v1
States: 2
Start: 0
acc-name: Buchi
Acceptance: 1 Inf(0)
AP: 1 "a"
--BODY--
State: 0
[0] 0 {0}
[0] 1
[!0] 0
State: 1
[t] 1
--END--
"#;

    #[test]
    fn nondeterministic_input_is_rejected_for_deterministic_automata() {
        use super::{HoaError, parse_omega_automaton_range};

        let end = NONDETERMINISTIC.len();
        assert!(parse_omega_automaton_range::<Linked>(NONDETERMINISTIC, 0, end).is_ok());
        match parse_omega_automaton_range::<Det<Linked>>(NONDETERMINISTIC, 0, end) {
            Err(HoaError::InRange {
                start: 0,
                end: e,
                source,
            }) => {
                assert_eq!(e, end);
                assert_eq!(*source, HoaError::NotDeterministic);
            }
            other => panic!("unexpected result: {:?}", other.map(|_| ())),
        }
    }

    #[test]
    fn invalid_input_reports_a_parse_error() {
        use super::{HoaError, parse_omega_automaton_range};

        let garbage = "HOA: v1\nthis is not an automaton\n--END--";
        match parse_omega_automaton_range::<Det<Linked>>(garbage, 0, garbage.len()) {
            Err(HoaError::InRange { source, .. }) => {
                assert!(matches!(*source, HoaError::Parse(_)));
            }
            other => panic!("unexpected result: {:?}", other.map(|_| ())),
        }
    }

    /// Parses `hoa` and returns the error that caused the failure, without the range information.
    fn failure(hoa: &str) -> super::HoaError {
        match super::parse_omega_automaton_range::<Linked>(hoa, 0, hoa.len()) {
            Err(super::HoaError::InRange { source, .. }) => *source,
            Err(other) => other,
            Ok(_) => panic!("expected the input to be rejected"),
        }
    }

    fn hoa_with(aps: &str, start: &str, body: &str) -> String {
        format!(
            "HOA: v1\nStates: 2\n{start}\nacc-name: Buchi\nAcceptance: 1 Inf(0)\n{aps}\n--BODY--\n{body}\n--END--\n"
        )
    }

    #[test]
    fn automaton_without_atomic_propositions_is_an_error() {
        use super::{HoaError, PropAlphabetError};
        let hoa = hoa_with("AP: 0", "Start: 0", "State: 0\n[t] 0 {0}\nState: 1\n[t] 1");
        assert_eq!(
            failure(&hoa),
            HoaError::Alphabet(PropAlphabetError::NoAtomicPropositions)
        );
    }

    #[test]
    fn automaton_with_too_many_atomic_propositions_is_an_error() {
        use super::{HoaError, PropAlphabetError};
        let hoa = hoa_with(
            "AP: 7 \"a\" \"b\" \"c\" \"d\" \"e\" \"f\" \"g\"",
            "Start: 0",
            "State: 0\n[t] 0 {0}\nState: 1\n[t] 1",
        );
        assert!(matches!(
            failure(&hoa),
            HoaError::Alphabet(PropAlphabetError::TooManyAtomicPropositions { count: 7, .. })
        ));
    }

    #[test]
    fn state_ids_must_be_contiguous() {
        use super::HoaError;
        let hoa = hoa_with(
            "AP: 1 \"a\"",
            "Start: 0",
            "State: 0\n[t] 0 {0}\nState: 5\n[t] 5",
        );
        assert_eq!(failure(&hoa), HoaError::StateOrder { position: 1, id: 5 });
    }

    #[test]
    fn multiple_initial_states_are_an_error() {
        use super::HoaError;
        let hoa = hoa_with(
            "AP: 1 \"a\"",
            "Start: 0\nStart: 1",
            "State: 0\n[t] 0 {0}\nState: 1\n[t] 1",
        );
        assert_eq!(failure(&hoa), HoaError::UnsupportedStartStates(2));
    }

    #[test]
    fn alternating_automata_are_an_error() {
        use super::HoaError;
        let hoa = hoa_with(
            "AP: 1 \"a\"",
            "Start: 0",
            "State: 0\n[t] 0&1 {0}\nState: 1\n[t] 1",
        );
        assert_eq!(failure(&hoa), HoaError::UnsupportedAlternation);
    }
}
