//! Python bindings for the `automata` crate (extension module `automata._automata`).

mod alphabet;
mod class;
mod dfa;
mod error;
mod game;
mod hoa;
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
    m.add_function(wrap_pyfunction!(hoa::parse_hoa, m)?)?;
    m.add_function(wrap_pyfunction!(hoa::parse_hoa_all, m)?)?;
    m.add_class::<alphabet::PyCharAlphabet>()?;
    m.add_class::<alphabet::PyPropAlphabet>()?;
    m.add_class::<dfa::PyDfa>()?;
    m.add_class::<dfa::PyPropDfa>()?;
    m.add_class::<kind::PyOmegaWord>()?;
    m.add_class::<omega::PyDba>()?;
    m.add_class::<omega::PyPropDba>()?;
    m.add_class::<omega::PyDca>()?;
    m.add_class::<omega::PyPropDca>()?;
    m.add_class::<omega::PyDpa>()?;
    m.add_class::<omega::PyPropDpa>()?;
    m.add_class::<omega::PyDpaMaxEven>()?;
    m.add_class::<omega::PyPropDpaMaxEven>()?;
    m.add_class::<omega::PyDpaMinOdd>()?;
    m.add_class::<omega::PyPropDpaMinOdd>()?;
    m.add_class::<omega::PyDpaMaxOdd>()?;
    m.add_class::<omega::PyPropDpaMaxOdd>()?;
    m.add_class::<omega::PyDra>()?;
    m.add_class::<omega::PyPropDra>()?;
    m.add_class::<omega::PyDsa>()?;
    m.add_class::<omega::PyPropDsa>()?;
    m.add_class::<omega::PyDma>()?;
    m.add_class::<omega::PyPropDma>()?;
    m.add_class::<nondet::PyNfa>()?;
    m.add_class::<nondet::PyPropNfa>()?;
    m.add_class::<nondet::PyNba>()?;
    m.add_class::<nondet::PyPropNba>()?;
    m.add_class::<nondet::PyNca>()?;
    m.add_class::<nondet::PyPropNca>()?;
    m.add_class::<nondet::PyNpa>()?;
    m.add_class::<nondet::PyPropNpa>()?;
    m.add_class::<machines::PyMooreMachine>()?;
    m.add_class::<machines::PyPropMooreMachine>()?;
    m.add_class::<machines::PyMealyMachine>()?;
    m.add_class::<machines::PyPropMealyMachine>()?;
    m.add_class::<game::PyMaxEvenParityGame>()?;
    m.add_class::<game::PyMinEvenParityGame>()?;
    m.add_class::<game::PyMaxOddParityGame>()?;
    m.add_class::<game::PyMinOddParityGame>()?;
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
    m.add("GameError", py.get_type::<error::GameError>())?;
    m.add("NotPeriodicError", py.get_type::<error::NotPeriodicError>())?;
    Ok(())
}

define_stub_info_gatherer!(stub_info);
