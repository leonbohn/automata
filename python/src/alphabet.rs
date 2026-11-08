//! Python classes for alphabets.

use automata::alphabet::{Alphabet, CharAlphabet, PropAlphabet};
use pyo3::{exceptions::PyValueError, prelude::*};
use pyo3_stub_gen::derive::{gen_stub_pyclass, gen_stub_pymethods};

use crate::error::PyError;

/// A finite alphabet of single characters.
///
/// >>> a = CharAlphabet("ba")
/// >>> a.symbols
/// 'ab'
/// >>> len(a)
/// 2
#[gen_stub_pyclass]
#[pyclass(frozen, eq, name = "CharAlphabet", module = "automata._automata")]
#[derive(Clone, PartialEq, Eq)]
pub struct PyCharAlphabet(pub(crate) CharAlphabet);

#[gen_stub_pymethods]
#[pymethods]
impl PyCharAlphabet {
    /// Creates the alphabet with the given characters (sorted, duplicates are removed).
    #[new]
    fn new(symbols: &str) -> Self {
        Self(symbols.chars().collect())
    }

    /// The characters of the alphabet in sorted order.
    #[getter]
    fn symbols(&self) -> String {
        self.0.universe().collect()
    }

    fn __len__(&self) -> usize {
        self.0.size()
    }

    fn __repr__(&self) -> String {
        format!("CharAlphabet({:?})", self.symbols())
    }
}

/// A propositional alphabet: a symbol is a valuation of the atomic propositions, given as a
/// sequence of booleans (one per proposition, in the order of `aps`).
///
/// >>> a = PropAlphabet(["p", "q"])
/// >>> a.aps
/// ['p', 'q']
/// >>> len(a)
/// 4
#[gen_stub_pyclass]
#[pyclass(frozen, name = "PropAlphabet", module = "automata._automata")]
#[derive(Clone)]
pub struct PyPropAlphabet(pub(crate) PropAlphabet);

#[gen_stub_pymethods]
#[pymethods]
impl PyPropAlphabet {
    /// Creates the alphabet over the atomic propositions with the given names.
    ///
    /// Raises `PropAlphabetError` if there are no or too many propositions.
    #[new]
    fn new(aps: Vec<String>) -> PyResult<Self> {
        PropAlphabet::try_new(aps)
            .map(Self)
            .map_err(|e| PyError(e.into()).into())
    }

    /// The names of the atomic propositions.
    #[getter]
    fn aps(&self) -> Vec<String> {
        self.0.apnames().to_vec()
    }

    /// The number of symbols, i.e. `2 ** len(aps)`.
    fn __len__(&self) -> usize {
        self.0.size()
    }

    fn __repr__(&self) -> String {
        format!("PropAlphabet({:?})", self.0.apnames())
    }
}

/// Converts a python sequence of booleans into a valuation, checking its length.
pub(crate) fn valuation(alphabet: &PropAlphabet, bools: Vec<bool>) -> PyResult<Vec<bool>> {
    if bools.len() != alphabet.aps() as usize {
        return Err(PyValueError::new_err(format!(
            "a symbol needs {} booleans (one per proposition), got {}",
            alphabet.aps(),
            bools.len()
        )));
    }
    Ok(bools)
}
