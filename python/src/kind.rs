//! The two kinds of alphabets (`CharAlphabet`, `PropAlphabet`) and how Python values for symbols
//! and words are converted for each. Every automaton class exists once per kind.

use automata::{
    alphabet::{Alphabet, CharAlphabet, PropAlphabet, PropSymbol},
    word::{OmegaWord, ReducedOmegaWord},
};
use pyo3::{
    exceptions::{PyTypeError, PyValueError},
    prelude::*,
};
use pyo3_stub_gen::derive::{gen_stub_pyclass, gen_stub_pymethods};

use crate::alphabet::{PyCharAlphabet, PyPropAlphabet, valuation};

/// Symbol of the Rust alphabet of a kind.
pub type Sym<K> = <<K as Kind>::A as Alphabet>::Symbol;

/// Everything that differs between the automaton classes over a `CharAlphabet` and those over a
/// `PropAlphabet`: how Python values are turned into symbols and back.
pub trait Kind: 'static {
    /// The Rust alphabet.
    type A: Alphabet<Symbol: Clone + Send> + Clone + Send + Sync + 'static;
    /// The Python alphabet class.
    type PyAlphabet;
    /// How a single symbol is written in Python.
    type PySymbol<'py>: FromPyObject<'py, 'py>;
    /// How a finite word is read from Python.
    type PyWord<'py>: FromPyObject<'py, 'py>;
    /// How a finite word is returned to Python.
    type PyWordOut: for<'py> IntoPyObject<'py>;

    fn alphabet(a: &Self::PyAlphabet) -> Self::A;
    fn to_py_alphabet(a: Self::A) -> Self::PyAlphabet;
    /// Converts and validates a symbol (`ValueError` if it does not belong to the alphabet).
    fn symbol(a: &Self::A, s: Self::PySymbol<'_>) -> PyResult<Sym<Self>>;
    /// Converts a word. Symbols that the alphabet does not know are not an error here: no edge
    /// can carry them, so the run of the word ends and it is rejected.
    fn word(a: &Self::A, w: Self::PyWord<'_>) -> PyResult<Vec<Sym<Self>>>;
    fn word_out(w: Vec<Sym<Self>>) -> Self::PyWordOut;
    /// An edge label as shown to the user.
    fn label(e: &<Self::A as Alphabet>::Expression) -> String;
    /// Reads the words of an omega word.
    fn omega(a: &Self::A, w: &PyOmegaWord) -> PyResult<ReducedOmegaWord<Sym<Self>>>;
    fn omega_out(w: &ReducedOmegaWord<Sym<Self>>) -> PyOmegaWord;
}

/// Characters, see [`PyCharAlphabet`].
pub struct Chars;
/// Valuations of propositions, see [`PyPropAlphabet`].
pub struct Props;

impl Kind for Chars {
    type A = CharAlphabet;
    type PyAlphabet = PyCharAlphabet;
    type PySymbol<'py> = char;
    type PyWord<'py> = String;
    type PyWordOut = String;

    fn alphabet(a: &PyCharAlphabet) -> CharAlphabet {
        a.0.clone()
    }
    fn to_py_alphabet(a: CharAlphabet) -> PyCharAlphabet {
        PyCharAlphabet(a)
    }
    fn symbol(a: &CharAlphabet, s: char) -> PyResult<char> {
        if a.contains(s) {
            Ok(s)
        } else {
            Err(PyValueError::new_err(format!(
                "{s:?} is not in the alphabet"
            )))
        }
    }
    fn word(_: &CharAlphabet, w: String) -> PyResult<Vec<char>> {
        Ok(w.chars().collect())
    }
    fn word_out(w: Vec<char>) -> String {
        w.into_iter().collect()
    }
    fn label(e: &char) -> String {
        e.to_string()
    }
    fn omega(_: &CharAlphabet, w: &PyOmegaWord) -> PyResult<ReducedOmegaWord<char>> {
        match (&w.prefix, &w.period) {
            (Syms::Chars(p), Syms::Chars(c)) => Ok(ReducedOmegaWord::ultimately_periodic(
                p.chars().collect::<Vec<_>>(),
                c.chars().collect::<Vec<_>>(),
            )),
            _ => Err(PyTypeError::new_err(
                "this automaton reads words of characters, got a word over propositions",
            )),
        }
    }
    fn omega_out(w: &ReducedOmegaWord<char>) -> PyOmegaWord {
        let (p, c) = w.raw_word().split_at(w.loop_index());
        PyOmegaWord {
            prefix: Syms::Chars(p.iter().collect()),
            period: Syms::Chars(c.iter().collect()),
        }
    }
}

impl Kind for Props {
    type A = PropAlphabet;
    type PyAlphabet = PyPropAlphabet;
    type PySymbol<'py> = Vec<bool>;
    type PyWord<'py> = Vec<Vec<bool>>;
    type PyWordOut = Vec<Vec<bool>>;

    fn alphabet(a: &PyPropAlphabet) -> PropAlphabet {
        a.0.clone()
    }
    fn to_py_alphabet(a: PropAlphabet) -> PyPropAlphabet {
        PyPropAlphabet(a)
    }
    fn symbol(a: &PropAlphabet, s: Vec<bool>) -> PyResult<PropSymbol> {
        Ok(PropSymbol::from_bools(valuation(a, s)?))
    }
    fn word(a: &PropAlphabet, w: Vec<Vec<bool>>) -> PyResult<Vec<PropSymbol>> {
        w.into_iter().map(|s| Self::symbol(a, s)).collect()
    }
    fn word_out(w: Vec<PropSymbol>) -> Vec<Vec<bool>> {
        w.iter().map(PropSymbol::as_bools).collect()
    }
    fn label(e: &<PropAlphabet as Alphabet>::Expression) -> String {
        e.to_hoa_label()
    }
    fn omega(a: &PropAlphabet, w: &PyOmegaWord) -> PyResult<ReducedOmegaWord<PropSymbol>> {
        match (&w.prefix, &w.period) {
            (Syms::Props(p), Syms::Props(c)) => Ok(ReducedOmegaWord::ultimately_periodic(
                Self::word(a, p.clone())?,
                Self::word(a, c.clone())?,
            )),
            _ => Err(PyTypeError::new_err(
                "this automaton reads words over propositions, got a word of characters",
            )),
        }
    }
    fn omega_out(w: &ReducedOmegaWord<PropSymbol>) -> PyOmegaWord {
        let (p, c) = w.raw_word().split_at(w.loop_index());
        PyOmegaWord {
            prefix: Syms::Props(p.iter().map(PropSymbol::as_bools).collect()),
            period: Syms::Props(c.iter().map(PropSymbol::as_bools).collect()),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum Syms {
    Chars(String),
    Props(Vec<Vec<bool>>),
}

impl Syms {
    fn read(obj: &Bound<'_, PyAny>) -> PyResult<Self> {
        if let Ok(s) = obj.extract::<String>() {
            Ok(Self::Chars(s))
        } else if let Ok(w) = obj.extract::<Vec<Vec<bool>>>() {
            Ok(Self::Props(w))
        } else {
            Err(PyTypeError::new_err(
                "expected a string or a sequence of sequences of booleans",
            ))
        }
    }

    fn is_empty(&self) -> bool {
        match self {
            Self::Chars(s) => s.is_empty(),
            Self::Props(w) => w.is_empty(),
        }
    }

    fn to_py<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        match self {
            Self::Chars(s) => Ok(s.into_pyobject(py)?.into_any()),
            Self::Props(w) => Ok(w.into_pyobject(py)?.into_any()),
        }
    }
}

/// An ultimately periodic infinite word `prefix period^ω`. Both parts are strings (for automata
/// over a `CharAlphabet`) or sequences of symbols (for automata over a `PropAlphabet`).
///
/// >>> w = OmegaWord("ab", "c")
/// >>> w.prefix, w.period
/// ('ab', 'c')
/// >>> OmegaWord([[True]], [[False]]).period
/// [[False]]
#[gen_stub_pyclass]
#[pyclass(frozen, eq, name = "OmegaWord", module = "automata._automata")]
#[derive(Clone, PartialEq, Eq)]
pub struct PyOmegaWord {
    prefix: Syms,
    period: Syms,
}

#[gen_stub_pymethods]
#[pymethods]
impl PyOmegaWord {
    /// Creates the word. Raises `ValueError` if the period is empty and `TypeError` if the
    /// parts are not both strings or both sequences of symbols.
    #[new]
    fn new(prefix: &Bound<'_, PyAny>, period: &Bound<'_, PyAny>) -> PyResult<Self> {
        let (prefix, period) = (Syms::read(prefix)?, Syms::read(period)?);
        if std::mem::discriminant(&prefix) != std::mem::discriminant(&period) {
            return Err(PyTypeError::new_err(
                "prefix and period have to be of the same kind",
            ));
        }
        if period.is_empty() {
            return Err(PyValueError::new_err("the period must not be empty"));
        }
        Ok(Self { prefix, period })
    }

    /// The finite prefix.
    #[getter]
    fn prefix<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        self.prefix.to_py(py)
    }

    /// The period, repeated forever after the prefix.
    #[getter]
    fn period<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        self.period.to_py(py)
    }

    fn __repr__(&self) -> String {
        format!("OmegaWord({:?}, {:?})", self.prefix, self.period)
    }
}
