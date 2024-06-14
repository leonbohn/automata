use ::automata::prelude::*;
use pyo3::prelude::*;

#[pyclass(name = "DFA")]
pub struct PyDFA {
    inner: DFA,
}

#[pymethods]
impl PyDFA {
    #[new]
    #[pyo3(signature = (alphabet_size,initial_accepting=false))]
    pub fn new(alphabet_size: u8, initial_accepting: bool) -> Self {
        Self {
            inner: DFA::new_with_initial_color(
                CharAlphabet::of_size(alphabet_size as usize),
                initial_accepting,
            ),
        }
    }

    pub fn size(&self) -> usize {
        self.inner.size()
    }

    pub fn add_state(&mut self, accepting: bool) -> u32 {
        self.inner.add_state(accepting)
    }

    pub fn remove_state(&mut self, id: u32) -> Option<bool> {
        self.inner.remove_state(id)
    }

    pub fn set_accepting(&mut self, id: u32, accepting: bool) -> Option<bool> {
        let previous_color = self.inner.state_color(id)?;
        self.inner.set_state_color(id, accepting);
        Some(previous_color)
    }

    pub fn is_accepting(&self, id: u32) -> Option<bool> {
        self.inner.state_color(id)
    }

    pub fn add_edge(&mut self, source: u32, symbol: char, target: u32) -> Option<u32> {
        self.inner
            .add_edge((source, symbol, target))
            .map(|tup| tup.3)
    }

    pub fn remove_edge(&mut self, source: u32, symbol: char, target: u32) -> bool {
        let Some(removed) = self
            .inner
            .remove_edges_between_matching(source, target, symbol)
        else {
            return false;
        };
        assert!(removed.len() <= 1);
        removed.is_empty()
    }
}

/// Formats the sum of two numbers as string.
#[pyfunction]
fn sum_as_string(a: usize, b: usize) -> PyResult<String> {
    Ok((a + b).to_string())
}

/// A Python module implemented in Rust.
#[pymodule]
fn automata(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(sum_as_string, m)?)?;
    m.add_class::<PyDFA>()?;
    Ok(())
}
