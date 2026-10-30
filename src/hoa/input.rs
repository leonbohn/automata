use std::{collections::BTreeSet, io::BufRead, ops::Deref};

use crate::automaton::{
    AcceptanceMask, DeterministicOmegaAutomaton, OmegaAcceptanceCondition, OmegaAutomaton,
    RabinPair,
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
        let (acceptance_sets, formula) = value
            .iter()
            .find_map(|it| match it {
                hoars::HeaderItem::Acceptance(acceptance, cond) => Some((*acceptance, cond)),
                _ => None,
            })
            .map_or((None, None), |(n, c)| (Some(n), Some(c)));

        let name = value
            .iter()
            .find_map(|it| it.try_acceptance_name())
            .map(|(name, _)| name)
            .ok_or_else(|| HoaError::UnsupportedAcceptance("missing acc-name".into()))?;
        match name {
            hoars::AcceptanceName::Buchi => Ok(OmegaAcceptanceCondition::Buchi),
            hoars::AcceptanceName::Parity => {
                let sets = acceptance_sets.ok_or(HoaError::MissingAcceptanceSets)?;
                Ok(OmegaAcceptanceCondition::Parity(
                    0,
                    (sets as Int).saturating_sub(1),
                ))
            }
            hoars::AcceptanceName::Rabin => Ok(OmegaAcceptanceCondition::Rabin(read_pairs(
                formula.ok_or(HoaError::MissingAcceptanceSets)?,
                Operator::Or,
            )?)),
            hoars::AcceptanceName::Streett => Ok(OmegaAcceptanceCondition::Streett(read_pairs(
                formula.ok_or(HoaError::MissingAcceptanceSets)?,
                Operator::And,
            )?)),
            other => Err(HoaError::UnsupportedAcceptance(format!("{other:?}"))),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Operator {
    And,
    Or,
}

impl Operator {
    fn dual(self) -> Self {
        match self {
            Operator::And => Operator::Or,
            Operator::Or => Operator::And,
        }
    }
}

/// Collects the operands of nested applications of `op`, e.g. `a & (b & c)` yields `a, b, c`.
fn flatten<'a>(
    cond: &'a hoars::AcceptanceCondition,
    op: Operator,
    out: &mut Vec<&'a hoars::AcceptanceCondition>,
) {
    match (cond, op) {
        (hoars::AcceptanceCondition::And(l, r), Operator::And)
        | (hoars::AcceptanceCondition::Or(l, r), Operator::Or) => {
            flatten(l, op, out);
            flatten(r, op, out);
        }
        _ => out.push(cond),
    }
}

/// Reads the pairs of a Rabin condition (`pair_join` is [`Operator::Or`]) or a Streett condition
/// ([`Operator::And`]). The pairs are joined by `pair_join`. Inside a pair, the operands are
/// joined by the dual operator; of these, plain `Fin` atoms of Rabin pairs (`Inf` atoms of Streett
/// pairs) are collected in one set, while the other kind of atom may appear once as a group
/// of atoms joined by `pair_join` (Rabin: `Inf(1) | Inf(2)`, Streett: `Fin(0) & Fin(1)`).
fn read_pairs(
    formula: &hoars::AcceptanceCondition,
    pair_join: Operator,
) -> Result<Vec<RabinPair<Int>>, HoaError> {
    let unsupported = |what: &str| {
        HoaError::UnsupportedAcceptance(format!(
            "{what} in {:?} condition",
            pair_join_name(pair_join)
        ))
    };
    let mut disjuncts = vec![];
    flatten(formula, pair_join, &mut disjuncts);
    // The constant that is neutral inside a group, and that makes a whole pair irrelevant when it
    // is the pair itself or one of its operands: `f` for Rabin, `t` for Streett.
    let flag = pair_join == Operator::And;
    let mut pairs = vec![];
    'pairs: for pair in disjuncts {
        match pair {
            hoars::AcceptanceCondition::Boolean(b) if b.0 == flag => continue,
            hoars::AcceptanceCondition::Boolean(_) => {
                return Err(unsupported("constant pair"));
            }
            _ => {}
        }
        let mut items = vec![];
        flatten(pair, pair_join.dual(), &mut items);
        let mut single = BTreeSet::new();
        let mut group: Option<BTreeSet<Int>> = None;
        for item in items {
            match (item, pair_join) {
                (hoars::AcceptanceCondition::Boolean(b), _) => {
                    if b.0 == flag {
                        continue 'pairs;
                    }
                }
                (hoars::AcceptanceCondition::Fin(a), Operator::Or)
                | (hoars::AcceptanceCondition::Inf(a), Operator::And) => {
                    single
                        .insert(positive(a).ok_or_else(|| unsupported("negated acceptance set"))?);
                }
                _ => {
                    if group.is_some() {
                        return Err(unsupported("pair with several groups of acceptance sets"));
                    }
                    let mut atoms = vec![];
                    flatten(item, pair_join, &mut atoms);
                    let mut set = BTreeSet::new();
                    for atom in atoms {
                        match (atom, pair_join) {
                            (hoars::AcceptanceCondition::Inf(a), Operator::Or)
                            | (hoars::AcceptanceCondition::Fin(a), Operator::And) => {
                                set.insert(
                                    positive(a)
                                        .ok_or_else(|| unsupported("negated acceptance set"))?,
                                );
                            }
                            (hoars::AcceptanceCondition::Boolean(b), _) if b.0 == flag => {}
                            _ => return Err(unsupported("unexpected formula")),
                        }
                    }
                    group = Some(set);
                }
            }
        }
        let group = group.ok_or_else(|| unsupported("pair without a group of acceptance sets"))?;
        pairs.push(match pair_join {
            Operator::Or => RabinPair::new(single, group),
            Operator::And => RabinPair::new(group, single),
        });
    }
    Ok(pairs)
}

fn pair_join_name(op: Operator) -> &'static str {
    match op {
        Operator::Or => "Rabin",
        Operator::And => "Streett",
    }
}

fn positive(atom: &hoars::AcceptanceAtom) -> Option<Int> {
    match atom {
        hoars::AcceptanceAtom::Positive(i) => Int::try_from(*i).ok(),
        hoars::AcceptanceAtom::Negative(_) => None,
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

    use crate::automaton::{OmegaAcceptanceCondition, RabinPair};
    use crate::hoa::HoaError;

    fn pair_condition(
        name: &str,
        sets: u32,
        formula: &str,
    ) -> Result<OmegaAcceptanceCondition, HoaError> {
        let raw = format!(
            "HOA: v1\nStates: 1\nStart: 0\nacc-name: {name}\nAcceptance: {sets} {formula}\nAP: 1 \"a\"\n--BODY--\nState: 0\n[t] 0\n--END--\n"
        );
        let parsed = hoars::HoaRepresentation::try_from(raw.as_str()).expect("valid HOA syntax");
        OmegaAcceptanceCondition::try_from(parsed.header())
    }

    #[test]
    fn rabin_and_streett_conditions_are_read() {
        use crate::automaton::OmegaAcceptanceCondition::{Rabin, Streett};
        let pairs = vec![
            RabinPair::from_iters([0], [1]),
            RabinPair::from_iters([2], [3, 4]),
        ];
        assert_eq!(
            pair_condition(
                "Rabin 2",
                5,
                "(Fin(0) & Inf(1)) | (Fin(2) & (Inf(3) | Inf(4)))"
            ),
            Ok(Rabin(pairs.clone()))
        );
        assert_eq!(
            pair_condition(
                "Streett 2",
                5,
                "(Fin(0) | Inf(1)) & ((Fin(2)) | (Inf(3) | Inf(4)))"
            ),
            Ok(Streett(pairs))
        );
        // constants: the empty conditions, and pairs that are irrelevant
        assert_eq!(pair_condition("Rabin 0", 0, "f"), Ok(Rabin(vec![])));
        assert_eq!(pair_condition("Streett 0", 0, "t"), Ok(Streett(vec![])));
        assert_eq!(
            pair_condition("Rabin 2", 3, "(Fin(0) & f) | (t & Inf(1) & Fin(2))"),
            Ok(Rabin(vec![RabinPair::from_iters([2], [1])]))
        );
    }

    #[test]
    fn unrepresentable_pairs_are_rejected() {
        for (name, formula) in [
            ("Rabin 1", "Fin(0)"),
            ("Rabin 1", "Inf(0) & Inf(1)"),
            ("Rabin 1", "Fin(0) & Inf(!1)"),
            ("Streett 1", "Fin(0) | Fin(1)"),
            ("Streett 1", "Inf(0)"),
            ("Streett 1", "f"),
        ] {
            assert!(
                matches!(
                    pair_condition(name, 2, formula),
                    Err(HoaError::UnsupportedAcceptance(_))
                ),
                "{name} {formula}"
            );
        }
    }

    #[test]
    fn rabin_automaton_is_written_and_read_back() {
        use crate::hoa::{HoaString, WriteHoa};
        let text = "HOA: v1\nAP: 1 \"a\"\nStates: 1\nStart: 0\nacc-name: Rabin 1\nAcceptance: 2 (Fin(0)) & (Inf(1))\n--BODY--\nState: 0\n[0] 0 {1}\n[!0] 0 {0}\n--END--\n";
        let aut = HoaString::from(text.to_string())
            .pop::<Det<Linked>>()
            .expect("valid");
        assert_eq!(
            *aut.acceptance(),
            OmegaAcceptanceCondition::Rabin(vec![RabinPair::from_iters([0], [1])])
        );
        let again = HoaString::from(aut.to_hoa().unwrap())
            .pop::<Det<Linked>>()
            .unwrap();
        assert_eq!(again.acceptance(), aut.acceptance());
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
