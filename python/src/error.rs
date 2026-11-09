//! Python exceptions mirroring [`automata::Error`].

use automata::Error;
use pyo3::{PyErr, exceptions::PyNotImplementedError};
use pyo3_stub_gen::create_exception;

create_exception!(
    automata._automata,
    AutomataError,
    pyo3::exceptions::PyException,
    "Base class of all errors raised by `automata`."
);
create_exception!(
    automata._automata,
    HoaError,
    AutomataError,
    "A HOA automaton could not be read or written."
);
create_exception!(
    automata._automata,
    PropAlphabetError,
    AutomataError,
    "An alphabet is not a valid propositional alphabet."
);
create_exception!(
    automata._automata,
    BuilderError,
    AutomataError,
    "A transition system could not be built."
);
create_exception!(
    automata._automata,
    AcceptanceError,
    AutomataError,
    "The acceptance sets of an edge do not fit the acceptance condition."
);
create_exception!(
    automata._automata,
    GameError,
    AutomataError,
    "A game could not be solved."
);
create_exception!(
    automata._automata,
    NotPeriodicError,
    AutomataError,
    "A word is not ultimately periodic."
);

/// Newtype that carries an [`Error`] through `?` in functions returning `PyResult`.
/// (`From<Error> for PyErr` cannot be implemented here, both types are foreign.)
pub struct PyError(pub Error);

impl From<Error> for PyError {
    fn from(e: Error) -> Self {
        Self(e)
    }
}

impl From<PyError> for PyErr {
    fn from(PyError(e): PyError) -> Self {
        let msg = e.to_string();
        match e {
            Error::NotYetImplemented(_) => PyNotImplementedError::new_err(msg),
            Error::Hoa(_) => HoaError::new_err(msg),
            Error::PropAlphabet(_) => PropAlphabetError::new_err(msg),
            Error::Builder(_) => BuilderError::new_err(msg),
            Error::Acceptance(_) => AcceptanceError::new_err(msg),
            Error::Game(_) => GameError::new_err(msg),
            Error::NotPeriodic(_) => NotPeriodicError::new_err(msg),
            // `Error` is non_exhaustive
            _ => AutomataError::new_err(msg),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyo3::Python;

    #[test]
    fn errors_map_to_python_exceptions() {
        Python::initialize();
        Python::attach(|py| {
            let err = PyErr::from(PyError(Error::NotYetImplemented("x")));
            assert!(err.is_instance_of::<PyNotImplementedError>(py));
            let err = PyErr::from(PyError(Error::from(automata::word::NotPeriodicError)));
            assert!(err.is_instance_of::<NotPeriodicError>(py));
            assert!(err.is_instance_of::<AutomataError>(py));
        });
    }
}
