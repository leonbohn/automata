//! Python classes for deterministic finite automata.

use automata::{
    DTS, Void,
    alphabet::{Alphabet, CharAlphabet, PropAlphabet, PropSymbol},
    automaton::DFA,
    ts::{ForAlphabet, Sproutable, States, TransitionSystem, q},
};
use pyo3::{
    exceptions::{PyIndexError, PyValueError},
    prelude::*,
};
use pyo3_stub_gen::derive::{gen_stub_pyclass, gen_stub_pymethods};

use crate::alphabet::{PyCharAlphabet, PyPropAlphabet, valuation};

/// Everything that differs between the DFA classes: how Python values are turned into symbols.
trait Frontend {
    /// The Rust alphabet.
    type A: Alphabet<Symbol: Clone + Send> + Clone + Send + Sync + 'static;
    /// The Python alphabet class.
    type PyAlphabet;
    /// How a single symbol is written in Python.
    type PySymbol<'py>: FromPyObject<'py, 'py>;
    /// How a word is written in Python.
    type PyWord<'py>: FromPyObject<'py, 'py>;

    fn alphabet(a: &Self::PyAlphabet) -> Self::A;
    fn to_py_alphabet(a: Self::A) -> Self::PyAlphabet;
    fn symbol(a: &Self::A, s: Self::PySymbol<'_>) -> PyResult<<Self::A as Alphabet>::Symbol>;
    fn word(a: &Self::A, w: Self::PyWord<'_>) -> PyResult<Vec<<Self::A as Alphabet>::Symbol>>;
    fn label(e: &<Self::A as Alphabet>::Expression) -> String;
}

struct Chars;
struct Props;

impl Frontend for Chars {
    type A = CharAlphabet;
    type PyAlphabet = PyCharAlphabet;
    type PySymbol<'py> = char;
    type PyWord<'py> = String;

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
        // symbols outside of the alphabet have no transition, so the word is rejected
        Ok(w.chars().collect())
    }
    fn label(e: &char) -> String {
        e.to_string()
    }
}

impl Frontend for Props {
    type A = PropAlphabet;
    type PyAlphabet = PyPropAlphabet;
    type PySymbol<'py> = Vec<bool>;
    type PyWord<'py> = Vec<Vec<bool>>;

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
    fn label(e: &<PropAlphabet as Alphabet>::Expression) -> String {
        e.to_hoa_label()
    }
}

type Dfa<F> = DFA<DTS<<F as Frontend>::A, bool, Void>>;

type Sym<F> = <<F as Frontend>::A as Alphabet>::Symbol;

fn check_state(q: u32, num_states: usize) -> PyResult<u32> {
    if (q as usize) < num_states {
        Ok(q)
    } else {
        Err(PyValueError::new_err(format!(
            "state {q} does not exist, there are {num_states} states"
        )))
    }
}

/// Assembles the DFA; all states in the arguments have to exist (`accepting.len()` many states).
fn assemble<F: Frontend>(
    alphabet: &F::A,
    accepting: &[bool],
    initial: u32,
    edges: &[(u32, Sym<F>, u32)],
) -> Dfa<F> {
    let mut ts = DTS::<F::A, bool, Void>::for_alphabet(alphabet.clone());
    let states: Vec<_> = accepting.iter().map(|&acc| ts.add_state(acc)).collect();
    for (source, symbol, target) in edges {
        ts.add_edge((
            states[*source as usize],
            alphabet.make_expression(*symbol),
            states[*target as usize],
        ));
    }
    DFA::from((ts, states[initial as usize]))
}

fn build<F: Frontend>(
    alphabet: &F::PyAlphabet,
    num_states: u32,
    initial: u32,
    accepting: Vec<u32>,
    edges: Vec<(u32, F::PySymbol<'_>, u32)>,
) -> PyResult<Dfa<F>> {
    let n = num_states as usize;
    let alphabet = F::alphabet(alphabet);
    let mut flags = vec![false; n];
    for q in accepting {
        flags[check_state(q, n)? as usize] = true;
    }
    check_state(initial, n)?;
    let edges = edges
        .into_iter()
        .map(|(s, sym, t)| {
            Ok((
                check_state(s, n)?,
                F::symbol(&alphabet, sym)?,
                check_state(t, n)?,
            ))
        })
        .collect::<PyResult<Vec<_>>>()?;
    Ok(assemble::<F>(&alphabet, &flags, initial, &edges))
}

fn edges_from<F: Frontend>(dfa: &Dfa<F>, state: u32) -> PyResult<Vec<(u32, String, u32)>> {
    if state as usize >= dfa.ts().state_count() {
        return Err(PyIndexError::new_err(format!(
            "state {state} does not exist"
        )));
    }
    Ok(dfa
        .ts()
        .edges_from(q(state))
        .into_iter()
        .flatten()
        .map(|e| {
            (
                e.source().into(),
                F::label(e.expression()),
                e.target().into(),
            )
        })
        .collect())
}

macro_rules! dfa_class {
    ($name:ident, $py_name:literal, $front:ty, $alphabet:ty, $doc:literal) => {
        #[doc = $doc]
        #[gen_stub_pyclass]
        #[pyclass(frozen, name = $py_name, module = "automata._automata")]
        pub struct $name(Dfa<$front>);

        #[gen_stub_pymethods]
        #[pymethods]
        impl $name {
            /// Creates the DFA with states `0, ..., num_states - 1`. `edges` are triples
            /// `(source, symbol, target)`; a later edge replaces an earlier one with the same
            /// source and symbol. Raises `ValueError` for states that do not exist.
            #[new]
            #[pyo3(signature = (alphabet, num_states, initial, accepting, edges))]
            fn new(
                alphabet: &$alphabet,
                num_states: u32,
                initial: u32,
                accepting: Vec<u32>,
                edges: Vec<(u32, <$front as Frontend>::PySymbol<'_>, u32)>,
            ) -> PyResult<Self> {
                build::<$front>(alphabet, num_states, initial, accepting, edges).map(Self)
            }

            /// Whether the DFA accepts the word. Words that leave the DFA (missing edge) are
            /// rejected.
            fn accepts(
                &self,
                py: Python<'_>,
                word: <$front as Frontend>::PyWord<'_>,
            ) -> PyResult<bool> {
                let word = <$front as Frontend>::word(self.0.ts().alphabet(), word)?;
                Ok(py.detach(|| self.0.accepts(word)))
            }

            /// The number of states.
            #[getter]
            fn num_states(&self) -> usize {
                self.0.ts().state_count()
            }

            /// The number of edges.
            #[getter]
            fn num_edges(&self) -> usize {
                self.0
                    .ts()
                    .states()
                    .map(|s| self.0.ts().edges_from(s).into_iter().flatten().count())
                    .sum()
            }

            /// The initial state.
            #[getter]
            fn initial(&self) -> u32 {
                automata::Pointed::initial(&self.0).into()
            }

            /// The alphabet of the DFA.
            #[getter]
            fn alphabet(&self) -> $alphabet {
                <$front>::to_py_alphabet(self.0.ts().alphabet().clone())
            }

            /// The states `0, ..., num_states - 1`.
            fn states(&self) -> Vec<u32> {
                self.0.ts().states().map(u32::from).collect()
            }

            /// Whether the state is accepting. Raises `IndexError` if it does not exist.
            fn is_accepting(&self, state: u32) -> PyResult<bool> {
                edges_from::<$front>(&self.0, state)?;
                Ok(self.0.is_accepting(q(state)))
            }

            /// The edges leaving `state` as triples `(source, label, target)`. Raises
            /// `IndexError` if the state does not exist.
            fn edges_from(&self, state: u32) -> PyResult<Vec<(u32, String, u32)>> {
                edges_from::<$front>(&self.0, state)
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

dfa_class!(
    PyDfa,
    "DFA",
    Chars,
    PyCharAlphabet,
    "A deterministic finite automaton over a `CharAlphabet`; words are strings.\n\n>>> a = CharAlphabet(\"ab\")\n>>> even_a = DFA(a, 2, 0, [0], [(0, \"a\", 1), (0, \"b\", 0), (1, \"a\", 0), (1, \"b\", 1)])\n>>> even_a.accepts(\"abba\")\nTrue\n>>> even_a.accepts(\"ab\")\nFalse\n>>> even_a.num_states, even_a.num_edges\n(2, 4)"
);

dfa_class!(
    PyPropDfa,
    "PropDFA",
    Props,
    PyPropAlphabet,
    "A deterministic finite automaton over a `PropAlphabet`; a symbol is a sequence of booleans, a word a sequence of symbols. Edge labels are given by the same sequences and shown in HOA syntax (`0 & !1`).\n\n>>> a = PropAlphabet([\"p\"])\n>>> d = PropDFA(a, 2, 0, [1], [(0, [True], 1), (0, [False], 0), (1, [True], 1), (1, [False], 1)])\n>>> d.accepts([[False], [True]])\nTrue\n>>> d.accepts([[False]])\nFalse"
);

macro_rules! builder_class {
    ($name:ident, $py_name:literal, $front:ty, $alphabet:ty, $dfa:ident, $doc:literal) => {
        #[doc = $doc]
        #[gen_stub_pyclass]
        #[pyclass(name = $py_name, module = "automata._automata")]
        pub struct $name {
            alphabet: <$front as Frontend>::A,
            accepting: Vec<bool>,
            initial: Option<u32>,
            edges: Vec<(u32, Sym<$front>, u32)>,
        }

        #[gen_stub_pymethods]
        #[pymethods]
        impl $name {
            /// Creates an empty builder for the alphabet.
            #[new]
            fn new(alphabet: &$alphabet) -> Self {
                Self {
                    alphabet: <$front>::alphabet(alphabet),
                    accepting: vec![],
                    initial: None,
                    edges: vec![],
                }
            }

            /// Adds a state and returns its number (`0, 1, 2, ...`).
            #[pyo3(signature = (accepting = false))]
            fn add_state(&mut self, accepting: bool) -> u32 {
                self.accepting.push(accepting);
                (self.accepting.len() - 1) as u32
            }

            /// Adds an edge between existing states; an edge with the same source and symbol
            /// that was added earlier is replaced. Raises `ValueError` for unknown states or
            /// symbols.
            fn add_edge(
                &mut self,
                source: u32,
                symbol: <$front as Frontend>::PySymbol<'_>,
                target: u32,
            ) -> PyResult<()> {
                let n = self.accepting.len();
                let edge = (
                    check_state(source, n)?,
                    <$front>::symbol(&self.alphabet, symbol)?,
                    check_state(target, n)?,
                );
                self.edges.push(edge);
                Ok(())
            }

            /// Marks an existing state as accepting or rejecting.
            #[pyo3(signature = (state, accepting = true))]
            fn set_accepting(&mut self, state: u32, accepting: bool) -> PyResult<()> {
                let n = self.accepting.len();
                self.accepting[check_state(state, n)? as usize] = accepting;
                Ok(())
            }

            /// Sets the initial state, which has to exist.
            fn set_initial(&mut self, state: u32) -> PyResult<()> {
                self.initial = Some(check_state(state, self.accepting.len())?);
                Ok(())
            }

            /// Creates the DFA. Raises `ValueError` if no initial state was set. The builder
            /// can be used further.
            fn build(&self) -> PyResult<$dfa> {
                let initial = self
                    .initial
                    .ok_or_else(|| PyValueError::new_err("no initial state set"))?;
                Ok($dfa(assemble::<$front>(
                    &self.alphabet,
                    &self.accepting,
                    initial,
                    &self.edges,
                )))
            }
        }
    };
}

builder_class!(
    PyDfaBuilder,
    "DFABuilder",
    Chars,
    PyCharAlphabet,
    PyDfa,
    "Builds a `DFA` step by step.\n\n>>> b = DFABuilder(CharAlphabet(\"ab\"))\n>>> q0, q1 = b.add_state(accepting=True), b.add_state()\n>>> for s, c, t in [(q0, \"a\", q1), (q0, \"b\", q0), (q1, \"a\", q0), (q1, \"b\", q1)]:\n...     b.add_edge(s, c, t)\n>>> b.set_initial(q0)\n>>> b.build().accepts(\"abba\")\nTrue"
);

builder_class!(
    PyPropDfaBuilder,
    "PropDFABuilder",
    Props,
    PyPropAlphabet,
    PyPropDfa,
    "Builds a `PropDFA` step by step, see `DFABuilder`; symbols are sequences of booleans.\n\n>>> b = PropDFABuilder(PropAlphabet([\"p\"]))\n>>> q = b.add_state(accepting=True)\n>>> b.add_edge(q, [True], q)\n>>> b.set_initial(q)\n>>> b.build().accepts([[True], [True]])\nTrue"
);
