//! Python bindings for the `automata` crate (extension module `automata._automata`).

mod alphabet;
mod class;
mod dfa;
mod error;
mod kind;
mod machines;
mod nondet;
mod omega;

use pyo3::prelude::*;
use pyo3_stub_gen::{define_stub_info_gatherer, derive::gen_stub_pyfunction};

/// The version of the underlying Rust bindings.
#[gen_stub_pyfunction]
#[pyfunction]
fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[pymodule]
fn _automata(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add("__version__", version())?;
    m.add_function(wrap_pyfunction!(version, m)?)?;
    m.add_class::<alphabet::PyCharAlphabet>()?;
    m.add_class::<alphabet::PyPropAlphabet>()?;
    m.add_class::<dfa::PyDfa>()?;
    m.add_class::<dfa::PyPropDfa>()?;
    m.add_class::<kind::PyOmegaWord>()?;
    m.add_class::<omega::PyDba>()?;
    m.add_class::<omega::PyPropDba>()?;
    m.add_class::<omega::PyDcw>()?;
    m.add_class::<omega::PyPropDcw>()?;
    m.add_class::<omega::PyDpa>()?;
    m.add_class::<omega::PyPropDpa>()?;
    m.add_class::<omega::PyDra>()?;
    m.add_class::<omega::PyPropDra>()?;
    m.add_class::<omega::PyDma>()?;
    m.add_class::<omega::PyPropDma>()?;
    m.add_class::<nondet::PyNfa>()?;
    m.add_class::<nondet::PyPropNfa>()?;
    m.add_class::<nondet::PyNba>()?;
    m.add_class::<nondet::PyPropNba>()?;
    m.add_class::<nondet::PyNcw>()?;
    m.add_class::<nondet::PyPropNcw>()?;
    m.add_class::<nondet::PyNpa>()?;
    m.add_class::<nondet::PyPropNpa>()?;
    m.add_class::<machines::PyMooreMachine>()?;
    m.add_class::<machines::PyPropMooreMachine>()?;
    m.add_class::<machines::PyMealyMachine>()?;
    m.add_class::<machines::PyPropMealyMachine>()?;
    m.add_class::<dfa::PyDfaBuilder>()?;
    m.add_class::<dfa::PyPropDfaBuilder>()?;
    let py = m.py();
    m.add("AutomataError", py.get_type::<error::AutomataError>())?;
    m.add("HoaError", py.get_type::<error::HoaError>())?;
    m.add(
        "PropAlphabetError",
        py.get_type::<error::PropAlphabetError>(),
    )?;
    m.add("BuilderError", py.get_type::<error::BuilderError>())?;
    m.add("AcceptanceError", py.get_type::<error::AcceptanceError>())?;
    m.add("NotPeriodicError", py.get_type::<error::NotPeriodicError>())?;
    Ok(())
}

define_stub_info_gatherer!(stub_info);
