use std::ops::Deref;

use crate::{
    automaton::{AcceptanceMask, DeterministicOmegaAutomaton},
    hoa::HoaExpression,
    prelude::*,
};
use hoars::{HoaAutomaton, MAX_APS};
use tracing::trace;

use super::{HoaAlphabet, HoaString};

fn parse_omega_automaton_range(
    hoa: &str,
    start: usize,
    end: usize,
) -> Option<OmegaAutomaton<HoaAlphabet>> {
    match HoaAutomaton::try_from(&hoa[start..end]) {
        Ok(aut) => match OmegaAutomaton::try_from(aut) {
            Ok(aut) => Some(aut),
            Err(e) => {
                tracing::warn!("Encountered processing error {}", e);
                None
            }
        },
        Err(e) => {
            tracing::warn!("Encountered parsing error {}", e);
            None
        }
    }
}

pub fn pop_deterministic_omega_automaton(
    hoa: HoaString,
) -> Option<(DeterministicOmegaAutomaton<HoaAlphabet>, HoaString)> {
    let mut hoa = hoa;
    while let Some((aut, rest)) = pop_omega_automaton(hoa) {
        if let Some(det) = aut.to_deterministic() {
            return Some((det, rest));
        }
        trace!("Automaton was not deterministic, skipping");
        hoa = rest;
    }
    None
}

/// Tries to `pop` the foremost valid HOA automaton from the given [`HoaStream`].
/// If no valid automaton is found before the end of the stream is reached, the
/// function returns `None`.
pub fn pop_omega_automaton(hoa: HoaString) -> Option<(OmegaAutomaton<HoaAlphabet>, HoaString)> {
    const END_LEN: usize = "--END--".len();
    const ABORT_LEN: usize = "--ABORT--".len();

    match (hoa.0.find("--ABORT--"), hoa.0.find("--END--")) {
        (None, Some(pos)) => {
            trace!("Returnting first automaton, going up to position {pos}");
            let aut = parse_omega_automaton_range(&hoa.0, 0, pos + END_LEN)?;
            Some((
                aut,
                HoaString(hoa.0[pos + END_LEN..].trim_start().to_string()),
            ))
        }
        (Some(abort), None) => {
            trace!("Found only one automaton --ABORT--ed at {abort}, but no subsequent --END-- of automaton to parse.");
            None
        }
        (Some(abort), Some(end)) => {
            if abort < end {
                trace!("Found --ABORT-- before --END--, returning first automaton from {abort} to {end}");
                let aut = parse_omega_automaton_range(&hoa.0, abort + ABORT_LEN, end + END_LEN)?;
                Some((
                    aut,
                    HoaString(hoa.0[end + END_LEN..].trim_start().to_string()),
                ))
            } else {
                trace!("Found --END--, returning first automaton up to {end}");
                let aut = parse_omega_automaton_range(&hoa.0, 0, end + END_LEN)?;
                Some((
                    aut,
                    HoaString(hoa.0[end + END_LEN..].trim_start().to_string()),
                ))
            }
        }
        (None, None) => {
            trace!("No end of automaton found, there is no automaton to parse.");
            None
        }
    }
}

/// Considers the given HOA string as a single automaton and tries to parse it into an
/// [`OmegaAutomaton`].
pub fn hoa_to_ts(hoa: &str) -> Vec<OmegaAutomaton<HoaAlphabet>> {
    let mut out = vec![];
    for hoa_aut in hoars::parse_hoa_automata(hoa) {
        match hoa_aut.try_into() {
            Ok(aut) => out.push(aut),
            Err(e) => tracing::warn!("Encountered parsing error {}", e),
        }
    }
    out
}

impl TryFrom<&hoars::Header> for OmegaAcceptanceCondition {
    type Error = String;

    fn try_from(value: &hoars::Header) -> Result<Self, Self::Error> {
        let acceptance_sets = value.iter().find_map(|it| match it {
            hoars::HeaderItem::Acceptance(acceptance, _cond) => Some(*acceptance),
            _ => None,
        });

        match value.acceptance_name() {
            hoars::AcceptanceName::Buchi => Ok(OmegaAcceptanceCondition::Buchi),
            hoars::AcceptanceName::Parity => Ok(OmegaAcceptanceCondition::Parity(
                0,
                acceptance_sets.unwrap() as usize,
            )),
            _ => Err("Unsupported acceptance condition".to_string()),
        }
    }
}

impl TryFrom<HoaAutomaton> for OmegaAutomaton<HoaAlphabet> {
    type Error = String;
    fn try_from(value: HoaAutomaton) -> Result<Self, Self::Error> {
        let acc = value.header().try_into()?;
        let ts = hoa_automaton_to_nts(value);
        Ok(Self::new(ts, acc))
    }
}

/// Converts a [`HoaAutomaton`] into a [`NTS`] with the same semantics. This creates the appropriate
/// number of states and inserts transitions with the appropriate labels and colors.
pub fn hoa_automaton_to_nts(
    aut: HoaAutomaton,
) -> Initialized<NTS<HoaAlphabet, usize, AcceptanceMask>> {
    let aps = aut.num_aps();
    assert!(aps < MAX_APS);
    let mut ts = NTS::for_alphabet(HoaAlphabet::from_hoa_automaton(&aut));
    for (id, state) in aut.body().iter().enumerate() {
        assert_eq!(id, state.id() as usize);
        assert_eq!(id, ts.add_state(state.id() as usize));
    }
    for state in aut.body().iter() {
        for edge in state.edges() {
            let target = edge
                .state_conjunction()
                .get_singleton()
                .expect("Cannot yet deal with conjunctions of target states")
                as usize;
            let label = edge.label().deref().clone();
            let expr = HoaExpression::new(label, aps);

            let color: AcceptanceMask = edge.acceptance_signature().into();
            ts.add_edge(state.id() as usize, expr, target, color);
        }
    }

    let start = aut.start();
    assert_eq!(start.len(), 1);
    let initial = start[0]
        .get_singleton()
        .expect("Initial state must be a singleton") as usize;

    ts.with_initial(initial)
}

#[cfg(test)]
mod tests {
    use tracing::debug;

    use crate::{hoa::HoaString, TransitionSystem};

    #[test_log::test]
    fn hoa_tdpa() {
        let raw_hoa = r#"
        HOA: v1
        States: 2
        Start: 0
        acc-name: Rabin 1
        Acceptance: 2 (Fin(0) & Inf(1))
        AP: 2 "a" "b"
        --BODY--
        State: 0 "a U b"   /* An example of named state */
        [0 & !1] 0 {0}
        [1] 1 {0}
        State: 1
        [t] 1 {1}
        --END--
        "
    }

    #[test_log::test]
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
        assert_eq!(first.size(), 1);
        assert!(hoa.0.is_empty());
    }
}
