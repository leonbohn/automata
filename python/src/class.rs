//! Building blocks shared by the automaton classes: [`assemble`] creates the Rust automaton
//! from validated data and [`automaton_class!`] defines a Python class around it.

use automata::{
    alphabet::Alphabet,
    automaton::Automaton,
    ts::{ForAlphabet, IntoEdgeTuple, Sproutable},
};
use pyo3::{exceptions::PyValueError, prelude::*};

use crate::kind::{Kind, Sym};

/// Checks that `q` is one of `num_states` states.
pub fn check_state(q: u32, num_states: usize) -> PyResult<u32> {
    if (q as usize) < num_states {
        Ok(q)
    } else {
        Err(PyValueError::new_err(format!(
            "state {q} does not exist, there are {num_states} states"
        )))
    }
}

/// An edge `(source, symbol, color, target)` with validated states and symbol.
pub type Edge<K, C> = (u32, Sym<K>, C, u32);

/// Creates the automaton with one state per element of `state_colors`. Expects `initial` and the
/// states of the edges to be valid (see [`check_state`]). In a deterministic transition system
/// a later edge replaces an earlier one with the same source and overlapping symbol.
pub fn assemble<K, T, Sem>(
    alphabet: &K::A,
    state_colors: Vec<T::StateColor>,
    initial: u32,
    edges: &[Edge<K, T::EdgeColor>],
    semantics: Sem,
) -> Automaton<T, Sem>
where
    K: Kind,
    T: ForAlphabet<K::A> + Sproutable<Alphabet = K::A>,
    T::EdgeColor: Clone,
    (
        T::StateIndex,
        <K::A as Alphabet>::Expression,
        T::EdgeColor,
        T::StateIndex,
    ): IntoEdgeTuple<T>,
{
    let mut ts = T::for_alphabet(alphabet.clone());
    let states: Vec<_> = state_colors.into_iter().map(|c| ts.add_state(c)).collect();
    for (source, symbol, color, target) in edges {
        ts.add_edge((
            states[*source as usize],
            alphabet.make_expression(*symbol),
            color.clone(),
            states[*target as usize],
        ));
    }
    Automaton::from_parts_with_acceptance(ts, states[initial as usize], semantics)
}

/// Defines a Python class that wraps `Automaton<$ts, $sem>` over the kind `$kind`, with the
/// methods every class has. The tokens in `{ ... }` are more methods of the class (at least a
/// constructor); inside them `self.0` is the automaton.
///
/// `$edge` is the Python type of an edge as it is returned by `edges_from` and `$out` the
/// closure that builds it from `(source, label, &color, target)`.
macro_rules! automaton_class {
    (
        $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $ts:ty, $sem:ty,
        edge = $edge:ty, out = $out:expr, doc = $doc:expr,
        { $($extra:tt)* }
    ) => {
        #[doc = $doc]
        #[::pyo3_stub_gen::derive::gen_stub_pyclass]
        #[::pyo3::pyclass(frozen, name = $py_name, module = "automata._automata")]
        pub struct $name(pub(crate) ::automata::automaton::Automaton<$ts, $sem>);

        #[::pyo3_stub_gen::derive::gen_stub_pymethods]
        #[::pyo3::pymethods]
        impl $name {
            $($extra)*

            /// The number of states.
            #[getter]
            fn num_states(&self) -> usize {
                ::automata::ts::States::state_count(self.0.ts())
            }

            /// The number of edges.
            #[getter]
            fn num_edges(&self) -> usize {
                use ::automata::ts::{States, TransitionSystem};
                self.0
                    .ts()
                    .states()
                    .map(|s| self.0.ts().edges_from(s).into_iter().flatten().count())
                    .sum()
            }

            /// The initial state.
            #[getter]
            fn initial(&self) -> u32 {
                ::automata::Pointed::initial(&self.0).into()
            }

            /// The alphabet of the automaton.
            #[getter]
            fn alphabet(&self) -> $pyalpha {
                use ::automata::ts::TransitionSystem;
                <$kind as $crate::kind::Kind>::to_py_alphabet(self.0.ts().alphabet().clone())
            }

            /// The states `0, ..., num_states - 1`.
            fn states(&self) -> Vec<u32> {
                use ::automata::ts::States;
                self.0.ts().states().map(u32::from).collect()
            }

            /// The edges leaving `state`, as `(source, label, target)` or, if edges have a
            /// color, `(source, label, color, target)`. Raises `IndexError` if the state does
            /// not exist.
            fn edges_from(&self, state: u32) -> ::pyo3::PyResult<Vec<$edge>> {
                use ::automata::ts::{States, TransitionSystem, q};
                if state as usize >= self.0.ts().state_count() {
                    return Err(::pyo3::exceptions::PyIndexError::new_err(format!(
                        "state {state} does not exist"
                    )));
                }
                Ok(self
                    .0
                    .ts()
                    .edges_from(q(state))
                    .into_iter()
                    .flatten()
                    .map(|e| {
                        ($out)(
                            u32::from(e.source()),
                            <$kind as $crate::kind::Kind>::label(e.expression()),
                            e.color(),
                            u32::from(e.target()),
                        )
                    })
                    .collect())
            }

            fn __repr__(&self) -> String {
                format!(
                    concat!($py_name, "(states={}, edges={})"),
                    self.num_states(),
                    self.num_edges()
                )
            }
        }
    };
}
pub(crate) use automaton_class;
