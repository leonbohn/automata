use std::ops::Deref;

use crate::{automaton::AcceptanceMask, hoa::HoaExpression, prelude::*};
use hoars::{HoaAutomaton, MAX_APS};

use super::{HoaAlphabet, HoaStream};

/// Tries to `pop` the foremost valid HOA automaton from the given [`HoaStream`].
/// If no valid automaton is found before the end of the stream is reached, the
/// function returns `None`.
pub fn pop_omega_automaton(
    hoa_stream: HoaStream,
) -> Option<(OmegaAutomaton<HoaAlphabet>, HoaStream)> {
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
        if !value.acceptance_name().is_parity() {
            return Err("Unhandled acceptance type".to_string());
        }
        Ok(OmegaAcceptanceCondition::Parity)
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
    #[test]
    fn hoa_tdba() {
        let aut_hoa = r#"
        HOA: v1
        States: 3
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 1
        [!0]  2
        State: 1  /* former state 0 */
        [0] 1 {0}
        [!0] 2 {0}
        State: 2  /* former state 1 */
        [0] 1
        [!0] 2
        --END--
        "#;
    }
}
