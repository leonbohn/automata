//! Reading automata in the HOA format: the conversions from the generic `OmegaAutomaton` of the
//! crate (acceptance sets as bit masks) to the classes of this module, and `parse_hoa`/
//! `parse_hoa_all`. Everything is read over a `PropAlphabet`.
//!
//! The reader of the crate knows the Büchi, co-Büchi, parity (all four kinds), Rabin and Streett
//! conditions. Rabin and Streett automata carry a *set* of acceptance sets on every edge, which the
//! classes `DRA` and `DSA` (one color per edge) get by numbering the distinct sets, see
//! [`renumber_masks`].

use std::collections::{BTreeMap, BTreeSet};

use automata::{
    DTS, Error, Int, NTS, Void,
    alphabet::PropAlphabet,
    automaton::{
        AcceptanceError, AcceptanceMask, Automaton, BuchiCondition, CoBuchiCondition,
        DeterministicOmegaAutomaton, Existential, MaxEvenParityCondition, MaxOddParityCondition,
        MinEvenParityCondition, MinOddParityCondition, NondeterministicOmegaAutomaton,
        OmegaAcceptanceCondition, ParityKind, RabinCondition, RabinPair, StreettCondition,
    },
    hoa::{HoaError, HoaRepresentation, input::HoaStorage},
    representation::IntoTransitions,
    ts::{Linked, States, TransitionSystem},
};
use pyo3::{prelude::*, types::PyAny};
use pyo3_stub_gen::derive::gen_stub_pyfunction;

use crate::error::PyError;
use crate::nondet::{PyPropNba, PyPropNcw, PyPropNpa};
use crate::omega::{
    PyPropDba, PyPropDcw, PyPropDpa, PyPropDpaMaxEven, PyPropDpaMaxOdd, PyPropDpaMinOdd, PyPropDra,
    PyPropDsa,
};

type Parsed = NondeterministicOmegaAutomaton<PropAlphabet>;
type ParsedDet = DeterministicOmegaAutomaton<PropAlphabet>;
type BuchiDet = Automaton<DTS<PropAlphabet, Void, bool>, BuchiCondition>;
type BoolNondet<C> = Automaton<NTS<PropAlphabet, Void, bool>, Existential<C>>;
type BuchiNondet = BoolNondet<BuchiCondition>;
type CoBuchiDet = Automaton<DTS<PropAlphabet, Void, bool>, CoBuchiCondition>;
type CoBuchiNondet = BoolNondet<CoBuchiCondition>;
type ParityDet = Automaton<DTS<PropAlphabet, Void, Int>, MinEvenParityCondition>;
type ParityNondet = Automaton<NTS<PropAlphabet, Void, Int>, Existential<MinEvenParityCondition>>;
/// A deterministic parity automaton whose condition is the typed counterpart of a [`ParityKind`].
type ParityKindDet<C> = Automaton<DTS<PropAlphabet, Void, Int>, C>;
type RabinDet = Automaton<DTS<PropAlphabet, Void, Int>, RabinCondition<Int>>;
type StreettDet = Automaton<DTS<PropAlphabet, Void, Int>, StreettCondition<Int>>;

/// The parts of `text` that end with `--END--` and contain a body.
fn chunks(text: &str) -> Vec<&str> {
    let found: Vec<_> = text
        .split_inclusive("--END--")
        .filter(|chunk| chunk.contains("--BODY--"))
        .collect();
    // nothing found: let the parser explain what is wrong with the whole text
    if found.is_empty() { vec![text] } else { found }
}

fn parse_chunk(chunk: &str) -> Result<Parsed, Fail> {
    let representation = HoaRepresentation::try_from(chunk.trim()).map_err(HoaError::from)?;
    // without a `States:` item, the reader of the crate panics on edges to states that do not exist
    let states = representation.body().len();
    let start = representation.start();
    let targets = start.iter().copied().chain(
        representation
            .body()
            .iter()
            .flat_map(|q| q.edges().iter().map(|e| e.state_conjunction())),
    );
    for target in targets.filter_map(|conjunction| conjunction.get_singleton()) {
        if target as usize >= states {
            return Err(Fail::Invalid(format!(
                "the state {target} does not exist, there are {states} states"
            )));
        }
    }
    Ok(Linked::from_hoa(representation)?)
}

fn parse_first(text: &str) -> Result<Parsed, Fail> {
    parse_chunk(chunks(text)[0])
}

fn parse_first_det(text: &str) -> Result<ParsedDet, Fail> {
    parse_first(text)?
        .try_into_deterministic()
        .map_err(|_| HoaError::NotDeterministic.into())
}

fn wrong_acceptance(found: &OmegaAcceptanceCondition, wanted: &str) -> Fail {
    HoaError::UnsupportedAcceptance(format!("{found:?}, but {wanted} is required")).into()
}

/// What can go wrong while reading: an error of the crate, or an input that the crate does not
/// check and would panic on.
enum Fail {
    Crate(Error),
    Invalid(String),
}

impl<E: Into<Error>> From<E> for Fail {
    fn from(e: E) -> Self {
        Self::Crate(e.into())
    }
}

impl From<Fail> for PyErr {
    fn from(fail: Fail) -> Self {
        match fail {
            Fail::Crate(e) => PyError(e).into(),
            Fail::Invalid(msg) => crate::error::HoaError::new_err(msg),
        }
    }
}

/// Runs `f` without the GIL and maps its error.
fn run<T: Send>(py: Python<'_>, f: impl FnOnce() -> Result<T, Fail> + Send) -> PyResult<T> {
    py.detach(f).map_err(PyErr::from)
}

/// The edges are colored `true` if they are in the acceptance set 0. `expected` (Büchi or
/// co-Büchi, called `name`) is the condition that the automaton has to have.
fn bool_det<C: Default>(
    aut: ParsedDet,
    expected: OmegaAcceptanceCondition,
    name: &str,
) -> Result<Automaton<DTS<PropAlphabet, Void, bool>, C>, Fail> {
    let (ts, initial, acceptance) = aut.into_parts();
    if acceptance != expected {
        return Err(wrong_acceptance(&acceptance, name));
    }
    Ok(ts
        .map_edge_colors(|mask| mask.as_bool())
        .with_initial(initial)
        .erase_state_colors()
        .collect())
}

fn bool_nondet<C: Default>(
    aut: Parsed,
    expected: OmegaAcceptanceCondition,
    name: &str,
) -> Result<BoolNondet<C>, Fail> {
    let (ts, initial, Existential(acceptance)) = aut.into_parts();
    if acceptance != expected {
        return Err(wrong_acceptance(&acceptance, name));
    }
    Ok(ts
        .map_edge_colors(|mask| mask.as_bool())
        .with_initial(initial)
        .erase_state_colors()
        .collect())
}

fn buchi_det(aut: ParsedDet) -> Result<BuchiDet, Fail> {
    bool_det(aut, OmegaAcceptanceCondition::Buchi, "Büchi")
}

fn buchi_nondet(aut: Parsed) -> Result<BuchiNondet, Fail> {
    bool_nondet(aut, OmegaAcceptanceCondition::Buchi, "Büchi")
}

fn co_buchi_det(aut: ParsedDet) -> Result<CoBuchiDet, Fail> {
    bool_det(aut, OmegaAcceptanceCondition::CoBuchi, "co-Büchi")
}

fn co_buchi_nondet(aut: Parsed) -> Result<CoBuchiNondet, Fail> {
    bool_nondet(aut, OmegaAcceptanceCondition::CoBuchi, "co-Büchi")
}

/// Every edge needs exactly one acceptance set (its priority), within `low..=high`.
fn check_priorities<T: States<EdgeColor = AcceptanceMask>>(
    ts: &T,
    low: Int,
    high: Int,
) -> Result<(), Fail> {
    for q in ts.states() {
        for edge in ts.edges_from(q).into_iter().flatten() {
            let priority = edge.color().try_as_priority().map_err(Error::from)?;
            if !(low..=high).contains(&priority) {
                return Err(AcceptanceError::PriorityOutOfRange {
                    priority,
                    low,
                    high,
                }
                .into());
            }
        }
    }
    Ok(())
}

/// Via `into_dpa` of the crate, which renumbers every parity kind (and Büchi and co-Büchi) to min
/// even. It needs exactly one acceptance set per edge and reports that Rabin and Streett automata
/// are not implemented.
fn parity_det(aut: ParsedDet) -> Result<ParityDet, Fail> {
    match aut.acceptance() {
        OmegaAcceptanceCondition::Parity(..)
        | OmegaAcceptanceCondition::Buchi
        | OmegaAcceptanceCondition::CoBuchi
        | OmegaAcceptanceCondition::Rabin(_)
        | OmegaAcceptanceCondition::Streett(_) => Ok(aut.into_dpa()?),
        other => Err(wrong_acceptance(
            other,
            "a parity, Büchi or co-Büchi condition",
        )),
    }
}

/// The automaton with exactly the parity condition `kind`, the priorities are kept.
fn parity_kind_det<C: Default>(aut: ParsedDet, kind: ParityKind) -> Result<ParityKindDet<C>, Fail> {
    let (ts, initial, acceptance) = aut.into_parts();
    let (low, high) = match acceptance {
        OmegaAcceptanceCondition::Parity(found, low, high) if found == kind => (low, high),
        other => {
            let name = format!(
                "parity {} {}",
                if kind.is_max() { "max" } else { "min" },
                if kind.is_even() { "even" } else { "odd" }
            );
            return Err(wrong_acceptance(&other, &name));
        }
    };
    check_priorities(&ts, low, high)?;
    Ok(ts
        .map_edge_colors(|mask| mask.as_priority())
        .with_initial(initial)
        .erase_state_colors()
        .collect())
}

/// The crate has no `into_dpa` for nondeterministic automata, so the priorities are validated
/// here.
fn parity_nondet(aut: Parsed) -> Result<ParityNondet, Fail> {
    let (ts, initial, Existential(acceptance)) = aut.into_parts();
    let (low, high) = match acceptance {
        OmegaAcceptanceCondition::Parity(ParityKind::MinEven, low, high) => (low, high),
        OmegaAcceptanceCondition::Parity(..) => {
            return Err(Error::NotYetImplemented(
                "reading nondeterministic parity automata that are not min even",
            )
            .into());
        }
        OmegaAcceptanceCondition::Rabin(_) | OmegaAcceptanceCondition::Streett(_) => {
            return Err(Error::NotYetImplemented(
                "conversion of nondeterministic Rabin and Streett automata",
            )
            .into());
        }
        other => return Err(wrong_acceptance(&other, "a parity condition")),
    };
    check_priorities(&ts, low, high)?;
    Ok(ts
        .map_edge_colors(|mask| mask.as_priority())
        .with_initial(initial)
        .erase_state_colors()
        .collect())
}

/// Numbers the distinct acceptance masks on the edges `0, 1, ...` in the order of their first
/// occurrence (the empty mask is one of them). Fails with more than `Int::MAX + 1` masks.
fn renumber_masks<T: States<EdgeColor = AcceptanceMask>>(
    ts: &T,
) -> Result<BTreeMap<AcceptanceMask, Int>, Fail> {
    let mut index = BTreeMap::new();
    for q in ts.states() {
        for edge in ts.edges_from(q).into_iter().flatten() {
            if index.contains_key(edge.color()) {
                continue;
            }
            let color = Int::try_from(index.len()).map_err(|_| {
                Fail::Invalid(format!(
                    "the edges have more than {} different sets of acceptance sets",
                    usize::from(Int::MAX) + 1
                ))
            })?;
            index.insert(edge.color().clone(), color);
        }
    }
    Ok(index)
}

/// The sets `(fin, inf)` of a pair, restricted to `universe` (the crate does not expose them).
/// Probes `satisfied_by_set` of the Rabin reading (no `fin` and some `inf`) and of the Streett
/// reading (no `fin` or some `inf`) on one- and two-element sets. If `fin` and `inf` are equal on
/// the universe, the pair is trivial in both readings (never or always satisfied) and both sets
/// are returned empty.
fn pair_parts(pair: &RabinPair<Int>, universe: &BTreeSet<Int>) -> (BTreeSet<Int>, BTreeSet<Int>) {
    let streett = StreettCondition::from([pair.clone()]);
    let rabin = |set: &[Int]| pair.satisfied_by_set(&set.iter().copied().collect());
    let streett = |set: &[Int]| streett.satisfied_by_set(&set.iter().copied().collect());
    // in `inf` only, in `fin` only
    let inf_only: BTreeSet<Int> = universe.iter().copied().filter(|&i| rabin(&[i])).collect();
    let fin_only: BTreeSet<Int> = universe
        .iter()
        .copied()
        .filter(|&i| !streett(&[i]))
        .collect();
    // the elements in both and in none of them cannot be told apart by one-element sets
    let both: BTreeSet<Int> = universe
        .iter()
        .copied()
        .filter(|i| !inf_only.contains(i) && !fin_only.contains(i))
        .filter(|&i| {
            if let Some(&a) = inf_only.first() {
                !rabin(&[i, a])
            } else if let Some(&b) = fin_only.first() {
                streett(&[i, b])
            } else {
                false
            }
        })
        .collect();
    (
        fin_only.union(&both).copied().collect(),
        inf_only.union(&both).copied().collect(),
    )
}

/// Translates the pairs, which talk about acceptance sets, to pairs about the colors of `index`:
/// a color is in `fin` (`inf`) if its mask meets the `fin` (`inf`) sets of the pair.
fn translate_pairs(
    pairs: &[RabinPair<Int>],
    index: &BTreeMap<AcceptanceMask, Int>,
) -> Vec<RabinPair<Int>> {
    let universe: BTreeSet<Int> = index.keys().flat_map(AcceptanceMask::iter).collect();
    let meeting = |sets: &BTreeSet<Int>| -> Vec<Int> {
        index
            .iter()
            .filter(|(mask, _)| mask.iter().any(|set| sets.contains(&set)))
            .map(|(_, &color)| color)
            .collect()
    };
    pairs
        .iter()
        .map(|pair| {
            let (fin, inf) = pair_parts(pair, &universe);
            RabinPair::from_iters(meeting(&fin), meeting(&inf))
        })
        .collect()
}

/// A Rabin (`rabin`) or Streett automaton with one color per distinct acceptance mask, `make`
/// builds the condition from the translated pairs.
fn pairs_det<C: Default>(
    aut: ParsedDet,
    rabin: bool,
    make: impl FnOnce(Vec<RabinPair<Int>>) -> C,
) -> Result<Automaton<DTS<PropAlphabet, Void, Int>, C>, Fail> {
    let (ts, initial, acceptance) = aut.into_parts();
    let pairs = match acceptance {
        OmegaAcceptanceCondition::Rabin(pairs) if rabin => pairs,
        OmegaAcceptanceCondition::Streett(pairs) if !rabin => pairs,
        other => {
            return Err(wrong_acceptance(
                &other,
                if rabin { "Rabin" } else { "Streett" },
            ));
        }
    };
    let index = renumber_masks(&ts)?;
    let pairs = translate_pairs(&pairs, &index);
    // every mask of an edge is in `index`
    let colored: Automaton<DTS<PropAlphabet, Void, Int>, C> = ts
        .map_edge_colors(|mask| index[&mask])
        .with_initial(initial)
        .erase_state_colors()
        .collect();
    Ok(colored.map_acceptance(|_| make(pairs)))
}

pub fn dba(py: Python<'_>, text: &str) -> PyResult<BuchiDet> {
    run(py, || buchi_det(parse_first_det(text)?))
}

pub fn dcw(py: Python<'_>, text: &str) -> PyResult<CoBuchiDet> {
    run(py, || co_buchi_det(parse_first_det(text)?))
}

pub fn dpa(py: Python<'_>, text: &str) -> PyResult<ParityDet> {
    run(py, || parity_det(parse_first_det(text)?))
}

pub fn dpa_kind<C: Default + Send>(
    py: Python<'_>,
    text: &str,
    kind: ParityKind,
) -> PyResult<ParityKindDet<C>> {
    run(py, || parity_kind_det(parse_first_det(text)?, kind))
}

pub fn dra(py: Python<'_>, text: &str) -> PyResult<RabinDet> {
    run(py, || {
        pairs_det(parse_first_det(text)?, true, |pairs| {
            RabinCondition::from(pairs)
        })
    })
}

pub fn dsa(py: Python<'_>, text: &str) -> PyResult<StreettDet> {
    run(py, || {
        pairs_det(parse_first_det(text)?, false, |pairs| {
            StreettCondition::from(pairs)
        })
    })
}

pub fn nba(py: Python<'_>, text: &str) -> PyResult<BuchiNondet> {
    run(py, || buchi_nondet(parse_first(text)?))
}

pub fn ncw(py: Python<'_>, text: &str) -> PyResult<CoBuchiNondet> {
    run(py, || co_buchi_nondet(parse_first(text)?))
}

pub fn npa(py: Python<'_>, text: &str) -> PyResult<ParityNondet> {
    run(py, || parity_nondet(parse_first(text)?))
}

/// An automaton of the most specific class for its branching and acceptance condition.
enum Any {
    Dba(PyPropDba),
    Dcw(PyPropDcw),
    Dpa(PyPropDpa),
    DpaMaxEven(PyPropDpaMaxEven),
    DpaMinOdd(PyPropDpaMinOdd),
    DpaMaxOdd(PyPropDpaMaxOdd),
    Dra(PyPropDra),
    Dsa(PyPropDsa),
    Nba(PyPropNba),
    Ncw(PyPropNcw),
    Npa(PyPropNpa),
}

impl Any {
    fn new(aut: Parsed) -> Result<Self, Fail> {
        use OmegaAcceptanceCondition as Cond;
        let unsupported = |what| Fail::from(Error::NotYetImplemented(what));
        match aut.try_into_deterministic() {
            Ok(det) => match det.acceptance().clone() {
                Cond::Buchi => Ok(Self::Dba(PyPropDba(buchi_det(det)?))),
                Cond::CoBuchi => Ok(Self::Dcw(PyPropDcw(co_buchi_det(det)?))),
                Cond::Parity(kind, ..) => match kind {
                    ParityKind::MinEven => Ok(Self::Dpa(PyPropDpa(parity_det(det)?))),
                    ParityKind::MaxEven => {
                        Ok(Self::DpaMaxEven(PyPropDpaMaxEven(parity_kind_det::<
                            MaxEvenParityCondition,
                        >(
                            det, kind
                        )?)))
                    }
                    ParityKind::MinOdd => Ok(Self::DpaMinOdd(PyPropDpaMinOdd(parity_kind_det::<
                        MinOddParityCondition,
                    >(
                        det, kind
                    )?))),
                    ParityKind::MaxOdd => Ok(Self::DpaMaxOdd(PyPropDpaMaxOdd(parity_kind_det::<
                        MaxOddParityCondition,
                    >(
                        det, kind
                    )?))),
                },
                Cond::Rabin(_) => Ok(Self::Dra(PyPropDra(pairs_det(det, true, |pairs| {
                    RabinCondition::from(pairs)
                })?))),
                Cond::Streett(_) => Ok(Self::Dsa(PyPropDsa(pairs_det(det, false, |pairs| {
                    StreettCondition::from(pairs)
                })?))),
                _ => Err(unsupported(
                    "reading deterministic automata that are not Büchi, co-Büchi, parity, Rabin or Streett",
                )),
            },
            Err(aut) => match aut.acceptance().0.clone() {
                Cond::Buchi => Ok(Self::Nba(PyPropNba(buchi_nondet(aut)?))),
                Cond::CoBuchi => Ok(Self::Ncw(PyPropNcw(co_buchi_nondet(aut)?))),
                Cond::Parity(..) => Ok(Self::Npa(PyPropNpa(parity_nondet(aut)?))),
                _ => Err(unsupported(
                    "reading nondeterministic automata that are not Büchi, co-Büchi or parity",
                )),
            },
        }
    }

    fn into_py(self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(match self {
            Self::Dba(a) => Py::new(py, a)?.into_any(),
            Self::Dcw(a) => Py::new(py, a)?.into_any(),
            Self::Dpa(a) => Py::new(py, a)?.into_any(),
            Self::DpaMaxEven(a) => Py::new(py, a)?.into_any(),
            Self::DpaMinOdd(a) => Py::new(py, a)?.into_any(),
            Self::DpaMaxOdd(a) => Py::new(py, a)?.into_any(),
            Self::Dra(a) => Py::new(py, a)?.into_any(),
            Self::Dsa(a) => Py::new(py, a)?.into_any(),
            Self::Nba(a) => Py::new(py, a)?.into_any(),
            Self::Ncw(a) => Py::new(py, a)?.into_any(),
            Self::Npa(a) => Py::new(py, a)?.into_any(),
        })
    }
}

/// Reads the first automaton in `text` (a HOA file may contain several) and returns it as an
/// instance of the most specific class: `PropDBA` for a deterministic Büchi automaton, `PropDCW`
/// for co-Büchi, `PropDPA`, `PropDPAMaxEven`, `PropDPAMinOdd` or `PropDPAMaxOdd` for the parity
/// kind of the file, `PropDRA` for Rabin and `PropDSA` for Streett. Automata that are not
/// deterministic give `PropNBA`, `PropNCW` or `PropNPA` (min even only). Rabin and Streett
/// colors are renumbered, see `PropDRA.from_hoa`. Raises `HoaError` if the text is not a
/// (supported) HOA automaton and `NotImplementedError` for acceptance conditions without a
/// class (nondeterministic Rabin and Streett, generalized conditions, ...) and for
/// nondeterministic parity conditions other than min even.
#[gen_stub_pyfunction]
#[pyfunction]
pub fn parse_hoa(py: Python<'_>, text: &str) -> PyResult<Py<PyAny>> {
    run(py, || Any::new(parse_first(text)?))?.into_py(py)
}

/// Like `parse_hoa`, but returns a list with all automata in `text`.
#[gen_stub_pyfunction]
#[pyfunction]
pub fn parse_hoa_all(py: Python<'_>, text: &str) -> PyResult<Vec<Py<PyAny>>> {
    run(py, || {
        chunks(text)
            .into_iter()
            .map(|chunk| Any::new(parse_chunk(chunk)?))
            .collect::<Result<Vec<_>, _>>()
    })?
    .into_iter()
    .map(|automaton| automaton.into_py(py))
    .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `pair_parts` finds the sets of every pair over a small universe, up to the equivalent
    /// trivial pair if `fin` and `inf` are equal there.
    #[test]
    fn pair_parts_recovers_the_pair() {
        let universe: BTreeSet<Int> = (0..4).collect();
        for fin in 0..16u8 {
            for inf in 0..16u8 {
                let sets = |bits: u8| (0..4).filter(move |i| bits >> i & 1 == 1);
                let pair = RabinPair::from_iters(sets(fin), sets(inf));
                let (found_fin, found_inf) = pair_parts(&pair, &universe);
                let found = RabinPair::new(found_fin.clone(), found_inf.clone());
                let streett = [pair.clone()];
                let streett_found = [found.clone()];
                for seen in 0..16u8 {
                    let seen: BTreeSet<Int> = sets(seen).collect();
                    assert_eq!(pair.satisfied_by_set(&seen), found.satisfied_by_set(&seen));
                    assert_eq!(
                        StreettCondition::from(streett.clone()).satisfied_by_set(&seen),
                        StreettCondition::from(streett_found.clone()).satisfied_by_set(&seen)
                    );
                }
                if fin != inf {
                    assert_eq!(found_fin, sets(fin).collect());
                    assert_eq!(found_inf, sets(inf).collect());
                }
            }
        }
    }
}
