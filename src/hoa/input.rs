use std::{collections::BTreeSet, io::BufRead};

use crate::automaton::{
    AcceptanceMask, DeterministicOmegaAutomaton, OmegaAcceptanceCondition, OmegaAutomaton,
    ParityKind, RabinPair,
};
use crate::ts::{DenseId, Det, ForAlphabet, Linked, LinkedTs, Sproutable, StateId, Storage};
use crate::{
    Int,
    alphabet::{PropAlphabet, PropExpression},
};
use hoars::{AbstractLabelExpression, HoaRepresentation};
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
            .acceptance()
            .map_or((None, None), |(n, c)| (Some(n), Some(c)));

        let name = value
            .acceptance_name()
            .ok_or_else(|| HoaError::UnsupportedAcceptance("missing acc-name".into()))?;
        match name {
            hoars::AcceptanceName::Buchi => Ok(OmegaAcceptanceCondition::Buchi),
            hoars::AcceptanceName::CoBuchi => Ok(OmegaAcceptanceCondition::CoBuchi),
            hoars::AcceptanceName::Parity => {
                let sets = acceptance_sets.ok_or(HoaError::MissingAcceptanceSets)?;
                let info = value
                    .acceptance_name_info()
                    .map_or(&[][..], |(_, info)| info);
                let kind = read_parity_kind(info, sets)?;
                let high = Int::try_from(sets.saturating_sub(1)).map_err(|_| {
                    HoaError::UnsupportedAcceptance(format!("parity with {sets} acceptance sets"))
                })?;
                Ok(OmegaAcceptanceCondition::Parity(kind, 0, high))
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

/// Reads the parameters `min|max even|odd n` of `acc-name: parity` and checks that `n` is the
/// number of acceptance sets of the `Acceptance:` item.
fn read_parity_kind(
    info: &[hoars::AcceptanceInfo],
    sets: hoars::Id,
) -> Result<ParityKind, HoaError> {
    use hoars::AcceptanceInfo::{Identifier, Int as Number};
    let inconsistent = |what: String| HoaError::InconsistentAcceptance(what);
    let [Identifier(extremum), Identifier(parity), Number(declared)] = info else {
        return Err(inconsistent(format!(
            "expected `parity min|max even|odd <sets>`, found parameters {info:?}"
        )));
    };
    if *declared != sets {
        return Err(inconsistent(format!(
            "acc-name declares {declared} acceptance sets, but Acceptance has {sets}"
        )));
    }
    match (extremum.as_str(), parity.as_str()) {
        ("min", "even") => Ok(ParityKind::MinEven),
        ("max", "even") => Ok(ParityKind::MaxEven),
        ("min", "odd") => Ok(ParityKind::MinOdd),
        ("max", "odd") => Ok(ParityKind::MaxOdd),
        _ => Err(inconsistent(format!(
            "unknown parity kind `{extremum} {parity}`"
        ))),
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
            ts,
            initial,
            crate::automaton::Existential(acceptance),
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

/// Folds a label (whose aliases are resolved) into an expression over `aps` propositions.
fn label_to_expression(
    aps: u8,
    label: &AbstractLabelExpression,
) -> Result<PropExpression, HoaError> {
    let fold = |parts: &[AbstractLabelExpression], unit: bool| {
        parts.iter().try_fold(
            if unit {
                PropExpression::universal(aps)
            } else {
                PropExpression::unsatisfiable(aps)
            },
            |acc, part| {
                let part = label_to_expression(aps, part)?;
                Ok::<_, HoaError>(if unit { acc & part } else { acc | part })
            },
        )
    };
    Ok(match label {
        AbstractLabelExpression::Boolean(true) => PropExpression::universal(aps),
        AbstractLabelExpression::Boolean(false) => PropExpression::unsatisfiable(aps),
        AbstractLabelExpression::Integer(ap) if *ap < aps as u16 => {
            PropExpression::proposition(aps, *ap as u8)
        }
        AbstractLabelExpression::Integer(ap) => {
            return Err(HoaError::UnknownProposition {
                ap: *ap as usize,
                num_aps: aps,
            });
        }
        AbstractLabelExpression::Alias(name) => {
            return Err(hoars::AliasError::Undefined(name.clone()).into());
        }
        AbstractLabelExpression::Negated(inner) => !label_to_expression(aps, inner)?,
        AbstractLabelExpression::Conjunction(parts) => fold(parts, true)?,
        AbstractLabelExpression::Disjunction(parts) => fold(parts, false)?,
    })
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
fn hoa_automaton_parts(mut aut: HoaRepresentation) -> Result<HoaParts, HoaError> {
    aut.unalias()?;
    // The number of atomic propositions is limited by [`PropAlphabet`], which rejects too many.
    let alphabet = PropAlphabet::try_from_apnames(aut.aps().iter())?;
    let aps = alphabet.aps();
    let mut ts: LinkedTs<PropAlphabet, Int, AcceptanceMask> = LinkedTs::for_alphabet(alphabet);

    for (position, state) in aut.body().iter().enumerate() {
        if state.id() as usize != position {
            return Err(HoaError::StateOrder {
                position,
                id: state.id(),
            });
        }
        let added = ts.add_state(state.id() as Int);
        debug_assert_eq!(added.into_usize(), position);
    }

    let mut acceptance: OmegaAcceptanceCondition = aut.header().try_into()?;
    // A parity edge without an acceptance set is legal HOA (Spot writes them): it contributes no
    // priority. It gets one that never wins and has the parity that the HOA formula gives on the
    // empty set: `high + 1` for the min kinds, and for the max kinds `-1`, i.e. all priorities are
    // shifted up by two (keeping their parity) and the neutral one is `1`. `high` grows accordingly.
    let mut shift = 0;
    let mut neutral = None;
    if let OmegaAcceptanceCondition::Parity(kind, _, high) = &mut acceptance {
        let uncolored = aut.body().iter().any(|state| {
            state
                .edges()
                .iter()
                .any(|e| e.effective_acceptance(state).is_empty())
        });
        if uncolored {
            shift = if kind.is_max() { 2 } else { 0 };
            let needed = usize::from(*high) + shift.max(1) as usize;
            *high = Int::try_from(needed)
                .map_err(|_| crate::automaton::AcceptanceError::PriorityOverflow { needed })?;
            neutral = Some(if shift > 0 { 1 } else { *high });
        }
    }

    // without a `States:` item nothing else checks that the targets exist
    let state_exists = |id: u32| (id as usize) < aut.body().len();
    for state in aut.body().iter() {
        for edge in state.edges() {
            let target = edge
                .state_conjunction()
                .get_singleton()
                .ok_or(HoaError::UnsupportedAlternation)?;
            if !state_exists(target) {
                return Err(HoaError::UnknownState(target));
            }
            let expr = label_to_expression(aps, edge.label())?;
            let mut color: AcceptanceMask = (&edge.effective_acceptance(state)).into();
            if let Some(neutral) = neutral {
                color = if color.iter().next().is_none() {
                    AcceptanceMask::from_iter([neutral])
                } else {
                    color.iter().map(|p| p + shift).collect()
                };
            }

            ts.add_edge((
                StateId::from(state.id()),
                expr,
                color,
                StateId::from(target),
            ));
        }
    }

    let start = aut.start();
    if start.len() != 1 {
        return Err(HoaError::UnsupportedStartStates(start.len()));
    }
    let initial = start[0]
        .get_singleton()
        .ok_or(HoaError::UnsupportedAlternation)?;
    if !state_exists(initial) {
        return Err(HoaError::UnknownState(initial));
    }

    Ok((ts, StateId::from(initial), acceptance))
}

#[cfg(test)]
mod tests {
    use crate::States;
    use crate::ts::{Det, Linked};
    use tracing::debug;

    use crate::hoa::{HoaString, WriteHoa};
    use hoars::AbstractLabelExpression;

    #[test]
    fn edge_labels_with_disjunction() {
        let raw_hoa = hoa_with_states(
            2,
            "AP: 3 \"a\" \"b\" \"c\"",
            "Start: 0",
            r#"
        State: 0
        [0&1 | 0&!2] 0 {0}
        [!0 | (!1&2)] 1
        State: 1
        [t] 1
        "#,
        );
        // Per edge: (source, target, acceptance, symbols satisfying the label), order-independent.
        let edges = |hoa: &str| {
            use crate::ts::{DenseId, TransitionSystem};
            use std::collections::BTreeSet;
            let aut = super::parse_omega_automaton_range::<Linked>(hoa, 0, hoa.len())
                .expect("disjunctive labels must be accepted");
            assert_eq!(aut.state_count(), 2);
            let mut edges = BTreeSet::new();
            for q in aut.states() {
                for e in aut.edges_from(q).into_iter().flatten() {
                    let mut syms: Vec<char> = e.expression().chars_iter().collect();
                    syms.sort();
                    edges.insert((
                        q.into_usize(),
                        e.target().into_usize(),
                        format!("{:?}", e.color()),
                        syms,
                    ));
                }
            }
            (edges, aut)
        };

        let (parsed, aut) = edges(&raw_hoa);
        // a, b, c with a=bit 0: a&b | a&!c = a&(b|!c) holds for 3 of 8 valuations, !a | (!b&c) for 5 of 8.
        let sizes: Vec<_> = parsed
            .iter()
            .map(|(q, t, _, s)| (*q, *t, s.len()))
            .collect();
        assert_eq!(sizes, vec![(0, 0, 3), (0, 1, 5), (1, 1, 8)]);

        let written = aut.to_hoa().expect("cannot write hoa");
        assert_eq!(
            edges(&written).0,
            parsed,
            "round trip changed the automaton"
        );
    }

    #[test]
    fn maximal_number_of_atomic_propositions_with_disjunction() {
        use crate::ts::TransitionSystem;
        let count = 31;
        let names = (0..count)
            .map(|i| format!("\"a{i}\""))
            .collect::<Vec<_>>()
            .join(" ");
        let hoa = hoa_with_states(
            2,
            &format!("AP: {count} {names}"),
            "Start: 0",
            "State: 0\n[0&30 | !1&!29] 0 {0}\n[!0&!30 | 15] 1\nState: 1\n[t] 1",
        );
        let edge_count = |hoa: &str| {
            let aut = super::parse_omega_automaton_range::<Linked>(hoa, 0, hoa.len())
                .expect("31 atomic propositions must be accepted");
            assert_eq!(aut.state_count(), 2);
            let n = aut.edges_from(0u32.into()).into_iter().flatten().count();
            (n, aut)
        };
        let (n, aut) = edge_count(&hoa);
        assert_eq!(n, 2);
        let written = aut.to_hoa().expect("cannot write hoa");
        assert_eq!(edge_count(&written).0, 2);
    }

    #[test]
    fn labels_with_aliases_unknown_propositions_and_many_propositions() {
        let parse = |header: &str, body: &str| {
            let hoa = hoa_with_states(1, header, "Start: 0", body);
            super::parse_omega_automaton_range::<Linked>(&hoa, 0, hoa.len())
        };
        let names = (0..8)
            .map(|i| format!("\"p{i}\""))
            .collect::<Vec<_>>()
            .join(" ");
        use crate::ts::TransitionSystem;
        // aliases are resolved, here over 8 propositions, i.e. BDDs
        let aut = parse(
            &format!("AP: 8 {names}\nAlias: @x 0 & !7"),
            "State: 0\n[@x | 3] 0 {0}",
        )
        .expect("aliases must be resolved");
        let edge = aut
            .edges_from(0u32.into())
            .into_iter()
            .flatten()
            .next()
            .unwrap();
        assert_eq!(edge.expression().sat_vals().count(), 128 + 64 - 32);
        // the parser already rejects these in files; the conversion reports them with types
        assert!(parse("AP: 1 \"a\"", "State: 0\n[1] 0 {0}").is_err());
        assert!(parse("AP: 1 \"a\"", "State: 0\n[@nope] 0 {0}").is_err());
        assert!(matches!(
            super::label_to_expression(1, &AbstractLabelExpression::Integer(1)),
            Err(HoaError::UnknownProposition { ap: 1, num_aps: 1 })
        ));
        assert!(matches!(
            super::label_to_expression(1, &AbstractLabelExpression::Alias("x".into())),
            Err(HoaError::UnresolvedAlias(hoars::AliasError::Undefined(_)))
        ));
    }

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
        // Since `hoars` 0.4 the parser itself rejects a missing `Acceptance:` item
        // (`ValidationError::MissingAcceptance`), so the header is built by hand here.
        let mut header = hoars::Header::new("v1");
        header
            .push(hoars::HeaderItem::AcceptanceName(
                hoars::AcceptanceName::Parity,
                vec![],
            ))
            .expect("acc-name is not repeated");
        assert_eq!(
            super::OmegaAcceptanceCondition::try_from(&header),
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

    #[test]
    fn parity_kinds_are_written_and_read_back() {
        use crate::automaton::ParityKind;
        use crate::hoa::{HoaString, WriteHoa};
        for (kind, name) in [
            (ParityKind::MinEven, "min even"),
            (ParityKind::MaxEven, "max even"),
            (ParityKind::MinOdd, "min odd"),
            (ParityKind::MaxOdd, "max odd"),
        ] {
            let condition = OmegaAcceptanceCondition::Parity(kind, 0, 2);
            let aut = crate::ts::Builder::default()
                .with_state_colors([crate::Void])
                .with_edges([(0, 'a', crate::automaton::AcceptanceMask::from_iter([1]), 0)])
                .into_automaton(0, condition.clone());
            let hoa = aut.to_hoa().unwrap();
            assert!(
                hoa.contains(&format!("acc-name: parity {name} 3\n")),
                "{hoa}"
            );
            let again = HoaString::from(hoa.clone()).pop::<Det<Linked>>().unwrap();
            assert_eq!(*again.acceptance(), condition, "{hoa}");
            assert_eq!(again.to_hoa().unwrap(), hoa);
        }
    }

    #[test]
    fn parity_names_are_checked_against_the_acceptance_item() {
        use crate::automaton::ParityKind;
        for (name, kind) in [
            ("parity min even 3", ParityKind::MinEven),
            ("parity max even 3", ParityKind::MaxEven),
            ("parity min odd 3", ParityKind::MinOdd),
            ("parity max odd 3", ParityKind::MaxOdd),
        ] {
            assert_eq!(
                pair_condition(name, 3, "Inf(0)"),
                Ok(OmegaAcceptanceCondition::Parity(kind, 0, 2))
            );
        }
        for name in [
            "parity",
            "parity min even",
            "parity min even 4",
            "parity middle even 3",
            "parity min fancy 3",
            "parity min even 3 extra",
        ] {
            assert!(
                matches!(
                    pair_condition(name, 3, "Inf(0)"),
                    Err(HoaError::InconsistentAcceptance(_))
                ),
                "{name}: {:?}",
                pair_condition(name, 3, "Inf(0)")
            );
        }
        assert!(matches!(
            pair_condition("parity min even 300", 300, "Inf(0)"),
            Err(HoaError::UnsupportedAcceptance(_))
        ));
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
    fn nondeterministic_input_accepts_with_some_run() {
        use crate::alphabet::PropSymbol;
        use crate::word::ReducedOmegaWord;

        let end = NONDETERMINISTIC.len();
        let aut = super::parse_omega_automaton_range::<Linked>(NONDETERMINISTIC, 0, end).unwrap();
        let [a, not_a] = [true, false].map(|b| PropSymbol::from_bools(vec![b]));
        // infinitely many `a`
        assert!(aut.accepts(ReducedOmegaWord::periodic(vec![not_a, a])));
        assert!(!aut.accepts(ReducedOmegaWord::ultimately_periodic(vec![a], vec![not_a])));
    }

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
        hoa_with_states(2, aps, start, body)
    }

    fn hoa_with_states(states: usize, aps: &str, start: &str, body: &str) -> String {
        format!(
            "HOA: v1\nStates: {states}\n{start}\nacc-name: Buchi\nAcceptance: 1 Inf(0)\n{aps}\n--BODY--\n{body}\n--END--\n"
        )
    }

    /// The edges of the parsed automaton as `(source, target, symbols, color)`, in a fixed order.
    fn colored_edges(hoa: &str) -> Vec<(usize, usize, Vec<char>, String)> {
        use crate::ts::{DenseId, TransitionSystem};
        let aut = super::parse_omega_automaton_range::<Linked>(hoa, 0, hoa.len()).unwrap();
        let mut edges = Vec::new();
        for q in aut.states() {
            for e in aut.edges_from(q).into_iter().flatten() {
                let mut symbols: Vec<char> = e.expression().chars_iter().collect();
                symbols.sort();
                edges.push((
                    q.into_usize(),
                    e.target().into_usize(),
                    symbols,
                    format!("{:?}", e.color()),
                ));
            }
        }
        edges.sort();
        edges
    }

    #[test]
    fn state_based_acceptance_is_put_on_the_outgoing_edges() {
        let state_based = hoa_with(
            "AP: 1 \"a\"",
            "Start: 0",
            "State: 0 {0}\n[0] 1\n[!0] 0\nState: 1\n[t] 0",
        );
        let edge_based = hoa_with(
            "AP: 1 \"a\"",
            "Start: 0",
            "State: 0\n[0] 1 {0}\n[!0] 0 {0}\nState: 1\n[t] 0",
        );
        let edges = colored_edges(&state_based);
        assert_eq!(edges, colored_edges(&edge_based));
        // the two edges of state 0 are in set 0, the one of state 1 in no set
        assert_eq!(edges[0].3, edges[1].3);
        assert_ne!(edges[0].3, edges[2].3);
    }

    #[test]
    fn state_based_and_edge_based_acceptance_on_one_edge_are_united() {
        let hoa = |body: &str| {
            format!(
                "HOA: v1\nStates: 2\nStart: 0\nacc-name: Rabin 1\nAcceptance: 2 Fin(0) & Inf(1)\nAP: 1 \"a\"\n--BODY--\n{body}\n--END--\n"
            )
        };
        let mixed = hoa("State: 0 {0}\n[0] 1 {1}\n[!0] 0\nState: 1\n[t] 0");
        let united = hoa("State: 0\n[0] 1 {0 1}\n[!0] 0 {0}\nState: 1\n[t] 0");
        assert_eq!(colored_edges(&mixed), colored_edges(&united));
    }

    #[test]
    fn state_based_acceptance_of_parity_automata_gives_the_priorities() {
        use crate::ts::TransitionSystem;
        let hoa = |body: &str| {
            format!(
                "HOA: v1\nStates: 2\nStart: 0\nacc-name: parity min even 3\nAcceptance: 3 Inf(0) | (Fin(1) & Inf(2))\nAP: 1 \"a\"\n--BODY--\n{body}\n--END--\n"
            )
        };
        let priorities = |text: &str| {
            let dpa = HoaString::from(text.to_string())
                .pop::<Det<Linked>>()
                .and_then(|a| a.into_dpa().ok())
                .expect("a parity automaton");
            let mut priorities: Vec<_> = dpa
                .states()
                .flat_map(|q| dpa.edges_from(q).into_iter().flatten())
                .map(|e| *e.color())
                .collect();
            priorities.sort();
            priorities
        };
        let state_based = hoa("State: 0 {0}\n[0] 1\n[!0] 0\nState: 1 {2}\n[t] 1");
        assert_eq!(priorities(&state_based), [0, 0, 2]);
        // a set on the state and another one on the edge give the edge two priorities
        let both = hoa("State: 0 {0}\n[0] 1 {1}\n[!0] 0\nState: 1\n[t] 1 {1}");
        let mut hoa = HoaString::from(both);
        assert!(hoa.pop::<Det<Linked>>().unwrap().into_dpa().is_err());
    }

    #[test]
    fn uncolored_parity_edges_get_the_neutral_priority() {
        use crate::alphabet::PropSymbol;
        use crate::word::ReducedOmegaWord;

        // (acc-name, Acceptance): the formula's value on the empty set is the expected result
        let cases = [
            ("min even 2", "Inf(0) | Fin(1)", true),
            ("min even 3", "Inf(0) | (Fin(1) & Inf(2))", false),
            ("min odd 2", "Fin(0) & Inf(1)", false),
            ("max even 2", "Fin(1) & Inf(0)", false),
            ("max odd 2", "Inf(1) | Fin(0)", true),
        ];
        let a = PropSymbol::from_bools(vec![true]);
        for (name, formula, accepting) in cases {
            let n = name.rsplit(' ').next().unwrap();
            let hoa = |body: &str| {
                let text = format!(
                    "HOA: v1\nStates: 1\nStart: 0\nacc-name: parity {name}\nAcceptance: {n} {formula}\nAP: 1 \"a\"\n--BODY--\nState: 0\n{body}\n--END--\n"
                );
                HoaString::from(text).pop::<Det<Linked>>().unwrap()
            };
            // a cycle without any colored edge
            let word = ReducedOmegaWord::periodic(vec![a]);
            assert_eq!(hoa("[t] 0").accepts(word.clone()), accepting, "{name}");
            assert_eq!(
                hoa("[t] 0").into_dpa().unwrap().accepts(word),
                accepting,
                "{name} as DPA"
            );
        }

        // a colored loop on `a` and an uncolored one on `!a`: the neutral priority never wins
        // against a real one, so the colored one decides
        let [a, not_a] = [true, false].map(|b| PropSymbol::from_bools(vec![b]));
        for (name, formula, color, accepting) in [
            ("min even 2", "Inf(0) | Fin(1)", 0, true),
            ("min even 2", "Inf(0) | Fin(1)", 1, false),
            ("max even 2", "Fin(1) & Inf(0)", 0, true),
            ("max even 2", "Fin(1) & Inf(0)", 1, false),
        ] {
            let text = format!(
                "HOA: v1\nStates: 1\nStart: 0\nacc-name: parity {name}\nAcceptance: 2 {formula}\nAP: 1 \"a\"\n--BODY--\nState: 0\n[0] 0 {{{color}}}\n[!0] 0\n--END--\n"
            );
            let aut = HoaString::from(text).pop::<Det<Linked>>().unwrap();
            let both = ReducedOmegaWord::periodic(vec![a, not_a]);
            assert_eq!(
                aut.into_dpa().unwrap().accepts(both),
                accepting,
                "{name} {color}"
            );
        }

        // the neutral priority needs a 257th acceptance set
        let formula = (0..256).fold(String::new(), |acc, i| {
            let atom = if i % 2 == 0 {
                format!("Inf({i})")
            } else {
                format!("Fin({i})")
            };
            if acc.is_empty() {
                atom
            } else {
                format!("{acc} | {atom}")
            }
        });
        let text = format!(
            "HOA: v1\nStates: 1\nStart: 0\nacc-name: parity min even 256\nAcceptance: 256 {formula}\nAP: 1 \"a\"\n--BODY--\nState: 0\n[t] 0\n--END--\n"
        );
        assert!(matches!(
            failure(&text),
            super::HoaError::Acceptance(crate::automaton::AcceptanceError::PriorityOverflow {
                needed: 256
            })
        ));
    }

    #[test]
    fn automaton_without_atomic_propositions_is_an_error() {
        use super::HoaError;
        use crate::alphabet::PropAlphabetError;
        let hoa = hoa_with("AP: 0", "Start: 0", "State: 0\n[t] 0 {0}\nState: 1\n[t] 1");
        assert_eq!(
            failure(&hoa),
            HoaError::Alphabet(PropAlphabetError::NoAtomicPropositions)
        );
    }

    #[test]
    fn edges_to_undefined_states_are_an_error_without_states_item() {
        use super::HoaError;
        let hoa = |start: u32, target: u32| {
            format!(
                "HOA: v1\nStart: {start}\nacc-name: Buchi\nAcceptance: 1 Inf(0)\nAP: 1 \"a\"\n--BODY--\nState: 0\n[t] {target}\n--END--\n"
            )
        };
        assert_eq!(failure(&hoa(0, 3)), HoaError::UnknownState(3));
        assert_eq!(failure(&hoa(2, 0)), HoaError::UnknownState(2));
        assert!(
            super::parse_omega_automaton_range::<Linked>(&hoa(0, 0), 0, hoa(0, 0).len()).is_ok()
        );
    }

    #[test]
    fn co_buchi_is_written_and_read_back() {
        use crate::hoa::{HoaString, WriteHoa};
        let aut = crate::ts::Builder::without_state_colors()
            .with_transitions([(0, 'a', true, 0), (0, 'b', false, 0)])
            .into_dca(0);
        let hoa = aut.to_hoa().unwrap();
        assert!(
            hoa.contains("acc-name: co-Buchi\nAcceptance: 1 Fin(0)\n"),
            "{hoa}"
        );
        let read = HoaString::from(hoa).pop::<Det<Linked>>().unwrap();
        assert_eq!(*read.acceptance(), OmegaAcceptanceCondition::CoBuchi);
    }

    #[test]
    fn automaton_with_too_many_atomic_propositions_is_an_error() {
        use super::HoaError;
        use crate::alphabet::PropAlphabetError;
        // The limit comes from `PropAlphabet` (32 variables for `u32`), i.e. at most 31 APs.
        let count = 32;
        let names = (0..count)
            .map(|i| format!("\"a{i}\""))
            .collect::<Vec<_>>()
            .join(" ");
        let hoa = hoa_with(
            &format!("AP: {count} {names}"),
            "Start: 0",
            "State: 0\n[t] 0 {0}\nState: 1\n[t] 1",
        );
        assert!(matches!(
            failure(&hoa),
            HoaError::Alphabet(PropAlphabetError::TooManyAtomicPropositions { count: 32, max: 31 })
        ));
    }

    #[test]
    fn state_ids_must_be_contiguous() {
        use super::HoaError;
        // `hoars` itself rejects ids beyond `States:`, so declare enough states for id 5 to be
        // in range; the error then comes from our contiguity check.
        let hoa = hoa_with_states(
            6,
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
