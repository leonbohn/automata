//! Reading automata in the HOA format: the conversions from the generic `OmegaAutomaton` of the
//! crate (acceptance sets as bit masks) to the classes of this module, and `parse_hoa`/
//! `parse_hoa_all`. Everything is read over a `PropAlphabet`.
//!
//! The reader of the crate knows the Büchi, parity, Rabin and Streett conditions (there is no
//! co-Büchi), so there are no `from_hoa` for the co-Büchi classes.

use automata::{
    DTS, Error, Int, NTS, Void,
    alphabet::PropAlphabet,
    automaton::{
        AcceptanceError, Automaton, BuchiCondition, DeterministicOmegaAutomaton, Existential,
        MinEvenParityCondition, NondeterministicOmegaAutomaton, OmegaAcceptanceCondition,
    },
    hoa::{AcceptanceInfo, AcceptanceName, HoaError, HoaRepresentation, input::HoaStorage},
    representation::IntoTransitions,
    ts::{Linked, States, TransitionSystem},
};
use pyo3::{prelude::*, types::PyAny};
use pyo3_stub_gen::derive::gen_stub_pyfunction;

use crate::error::PyError;
use crate::nondet::{PyPropNba, PyPropNpa};
use crate::omega::{PyPropDba, PyPropDpa};

type Parsed = NondeterministicOmegaAutomaton<PropAlphabet>;
type ParsedDet = DeterministicOmegaAutomaton<PropAlphabet>;
type BuchiDet = Automaton<DTS<PropAlphabet, Void, bool>, BuchiCondition>;
type BuchiNondet = Automaton<NTS<PropAlphabet, Void, bool>, Existential<BuchiCondition>>;
type ParityDet = Automaton<DTS<PropAlphabet, Void, Int>, MinEvenParityCondition>;
type ParityNondet = Automaton<NTS<PropAlphabet, Void, Int>, Existential<MinEvenParityCondition>>;

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
    // the reader of the crate treats every parity condition as min even
    if let Some((AcceptanceName::Parity, info)) = representation.header().acceptance_name_info()
        && info.iter().any(
            |i| matches!(i, AcceptanceInfo::Identifier(word) if word == "max" || word == "odd"),
        )
    {
        return Err(
            Error::NotYetImplemented("reading parity automata that are not min even").into(),
        );
    }
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

/// The edges are colored `true` if they are in the acceptance set 0.
fn buchi_det(aut: ParsedDet) -> Result<BuchiDet, Fail> {
    let (ts, initial, acceptance) = aut.into_parts();
    if acceptance != OmegaAcceptanceCondition::Buchi {
        return Err(wrong_acceptance(&acceptance, "Büchi"));
    }
    Ok(ts
        .map_edge_colors(|mask| mask.as_bool())
        .with_initial(initial)
        .erase_state_colors()
        .collect())
}

fn buchi_nondet(aut: Parsed) -> Result<BuchiNondet, Fail> {
    let (ts, initial, Existential(acceptance)) = aut.into_parts();
    if acceptance != OmegaAcceptanceCondition::Buchi {
        return Err(wrong_acceptance(&acceptance, "Büchi"));
    }
    Ok(ts
        .map_edge_colors(|mask| mask.as_bool())
        .with_initial(initial)
        .erase_state_colors()
        .collect())
}

/// Via `into_dpa` of the crate (every edge needs exactly one acceptance set), which reports
/// that Rabin and Streett automata are not implemented.
fn parity_det(aut: ParsedDet) -> Result<ParityDet, Fail> {
    match aut.acceptance() {
        OmegaAcceptanceCondition::Parity(..)
        | OmegaAcceptanceCondition::Rabin(_)
        | OmegaAcceptanceCondition::Streett(_) => Ok(aut.into_dpa()?),
        other => Err(wrong_acceptance(other, "a parity condition")),
    }
}

/// The crate has no `into_dpa` for nondeterministic automata, so the priorities are validated
/// here.
fn parity_nondet(aut: Parsed) -> Result<ParityNondet, Fail> {
    let (ts, initial, Existential(acceptance)) = aut.into_parts();
    let (low, high) = match acceptance {
        OmegaAcceptanceCondition::Parity(low, high) => (low, high),
        OmegaAcceptanceCondition::Rabin(_) | OmegaAcceptanceCondition::Streett(_) => {
            return Err(Error::NotYetImplemented(
                "conversion of nondeterministic Rabin and Streett automata",
            )
            .into());
        }
        other => return Err(wrong_acceptance(&other, "a parity condition")),
    };
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
    Ok(ts
        .map_edge_colors(|mask| mask.as_priority())
        .with_initial(initial)
        .erase_state_colors()
        .collect())
}

pub fn dba(py: Python<'_>, text: &str) -> PyResult<BuchiDet> {
    run(py, || buchi_det(parse_first_det(text)?))
}

pub fn dpa(py: Python<'_>, text: &str) -> PyResult<ParityDet> {
    run(py, || parity_det(parse_first_det(text)?))
}

pub fn nba(py: Python<'_>, text: &str) -> PyResult<BuchiNondet> {
    run(py, || buchi_nondet(parse_first(text)?))
}

pub fn npa(py: Python<'_>, text: &str) -> PyResult<ParityNondet> {
    run(py, || parity_nondet(parse_first(text)?))
}

/// An automaton of the most specific class for its branching and acceptance condition.
enum Any {
    Dba(PyPropDba),
    Dpa(PyPropDpa),
    Nba(PyPropNba),
    Npa(PyPropNpa),
}

impl Any {
    fn new(aut: Parsed) -> Result<Self, Fail> {
        use OmegaAcceptanceCondition as Cond;
        let unsupported = |what| Fail::from(Error::NotYetImplemented(what));
        match aut.try_into_deterministic() {
            Ok(det) => match det.acceptance().clone() {
                Cond::Buchi => Ok(Self::Dba(PyPropDba(buchi_det(det)?))),
                Cond::Parity(..) => Ok(Self::Dpa(PyPropDpa(parity_det(det)?))),
                _ => Err(unsupported(
                    "reading deterministic automata that are not Büchi or parity",
                )),
            },
            Err(aut) => match aut.acceptance().0.clone() {
                Cond::Buchi => Ok(Self::Nba(PyPropNba(buchi_nondet(aut)?))),
                Cond::Parity(..) => Ok(Self::Npa(PyPropNpa(parity_nondet(aut)?))),
                _ => Err(unsupported(
                    "reading nondeterministic automata that are not Büchi or parity",
                )),
            },
        }
    }

    fn into_py(self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(match self {
            Self::Dba(a) => Py::new(py, a)?.into_any(),
            Self::Dpa(a) => Py::new(py, a)?.into_any(),
            Self::Nba(a) => Py::new(py, a)?.into_any(),
            Self::Npa(a) => Py::new(py, a)?.into_any(),
        })
    }
}

/// Reads the first automaton in `text` (a HOA file may contain several) and returns it as an
/// instance of the most specific class: `PropDBA` for a deterministic Büchi automaton, `PropDPA`
/// for parity, `PropNBA` or `PropNPA` if the automaton is not deterministic. Raises `HoaError` if
/// the text is not a (supported) HOA automaton and `NotImplementedError` for acceptance conditions
/// without a class (Rabin, Streett) and for parity conditions other than min even.
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
