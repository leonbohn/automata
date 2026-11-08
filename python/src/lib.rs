//! Python bindings for the `automata` crate (extension module `automata._automata`).

mod alphabet;
mod class;
mod dfa;
mod error;
mod kind;
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
