//! Python classes for deterministic finite automata.

use automata::{
    DTS, Void,
    alphabet::Alphabet,
    automaton::{Disjointness, Emptiness, Equivalence, Inclusion},
    representation::CollectPointed,
    ts::{Pointed, TransitionSystem},
};
use pyo3::{exceptions::PyValueError, prelude::*};
use pyo3_stub_gen::derive::{gen_stub_pyclass, gen_stub_pymethods};

use crate::alphabet::{PyCharAlphabet, PyPropAlphabet};
use crate::class::{Edge, assemble, automaton_class, check_state};
use crate::kind::{Chars, Kind, Props};

/// Creates a finite-word automaton (states colored with `bool`, edges uncolored).
pub fn finite<K, T, Sem>(
    alphabet: &K::PyAlphabet,
    num_states: u32,
    initial: u32,
    accepting: Vec<u32>,
    edges: Vec<(u32, K::PySymbol<'_>, u32)>,
    semantics: Sem,
) -> PyResult<automata::automaton::Automaton<T, Sem>>
where
    K: Kind,
    T: automata::ts::ForAlphabet<K::A>
        + automata::ts::Sproutable<Alphabet = K::A, StateColor = bool, EdgeColor = Void>,
    (
        T::StateIndex,
        <K::A as Alphabet>::Expression,
        Void,
        T::StateIndex,
    ): automata::ts::IntoEdgeTuple<T>,
{
    let n = num_states as usize;
    let alphabet = K::alphabet(alphabet);
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
                K::symbol(&alphabet, sym)?,
                Void,
                check_state(t, n)?,
            ))
        })
        .collect::<PyResult<Vec<Edge<K, Void>>>>()?;
    Ok(assemble::<K, T, Sem>(
        &alphabet, flags, initial, &edges, semantics,
    ))
}

macro_rules! dfa_class {
    ($name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $doc:expr) => {
        automaton_class!(
            $name, $py_name, $kind, $pyalpha,
            DTS<<$kind as Kind>::A, bool, Void>, automata::automaton::ReachabilityCondition,
            edge = (u32, String, u32), out = |s, l, _c: &Void, t| (s, l, t), doc = $doc,
            {
                /// Creates the DFA with states `0, ..., num_states - 1`. `edges` are triples
                /// `(source, symbol, target)`; a later edge replaces an earlier one with the same
                /// source and symbol. Raises `ValueError` for states or symbols that do not exist.
                #[new]
                fn new(
                    alphabet: &$pyalpha,
                    num_states: u32,
                    initial: u32,
                    accepting: Vec<u32>,
                    edges: Vec<(u32, <$kind as Kind>::PySymbol<'_>, u32)>,
                ) -> PyResult<Self> {
                    finite::<$kind, _, _>(
                        alphabet, num_states, initial, accepting, edges, Default::default(),
                    )
                    .map(Self)
                }

                /// Whether the DFA accepts the word. Words that leave the DFA (missing edge) are
                /// rejected.
                fn accepts(
                    &self,
                    py: Python<'_>,
                    word: <$kind as Kind>::PyWord<'_>,
                ) -> PyResult<bool> {
                    let word = <$kind as Kind>::word(self.0.ts().alphabet(), word)?;
                    Ok(py.detach(|| self.0.accepts(word)))
                }

                /// Whether the state is accepting. Raises `IndexError` if it does not exist.
                fn is_accepting(&self, state: u32) -> PyResult<bool> {
                    self.edges_from(state)?;
                    Ok(self.0.is_accepting(automata::ts::q(state)))
                }

                /// The accepting states.
                fn accepting_states(&self) -> Vec<u32> {
                    self.0.accepting_states().map(u32::from).collect()
                }

                /// Whether the language is empty.
                fn is_empty(&self, py: Python<'_>) -> bool {
                    py.detach(|| Emptiness::of(&self.0).holds())
                }

                /// A shortest accepted word, or `None` if the language is empty.
                fn accepting_word(&self, py: Python<'_>) -> Option<<$kind as Kind>::PyWordOut> {
                    py.detach(|| Emptiness::of(&self.0).witness()).map(<$kind as Kind>::word_out)
                }

                /// Whether the language of `self` is contained in the one of `other`.
                fn included_in(&self, py: Python<'_>, other: &Self) -> PyResult<bool> {
                    crate::class::same_alphabet(self.0.ts().alphabet(), other.0.ts().alphabet())?;
                    Ok(py.detach(|| Inclusion::of(&self.0).within(&other.0).holds()))
                }

                /// A word accepted by `self` but not by `other`, or `None` if `self` is included
                /// in `other`.
                fn inclusion_counterexample(
                    &self,
                    py: Python<'_>,
                    other: &Self,
                ) -> PyResult<Option<<$kind as Kind>::PyWordOut>> {
                    crate::class::same_alphabet(self.0.ts().alphabet(), other.0.ts().alphabet())?;
                    Ok(py.detach(|| Inclusion::of(&self.0).within(&other.0).counterexample())
                            .map(<$kind as Kind>::word_out))
                }

                /// Whether both DFAs accept the same language.
                fn equivalent_to(&self, py: Python<'_>, other: &Self) -> PyResult<bool> {
                    crate::class::same_alphabet(self.0.ts().alphabet(), other.0.ts().alphabet())?;
                    Ok(py.detach(|| Equivalence::of(&self.0).and(&other.0).holds()))
                }

                /// A word that exactly one of the DFAs accepts, or `None` if they are equivalent.
                fn equivalence_counterexample(
                    &self,
                    py: Python<'_>,
                    other: &Self,
                ) -> PyResult<Option<<$kind as Kind>::PyWordOut>> {
                    crate::class::same_alphabet(self.0.ts().alphabet(), other.0.ts().alphabet())?;
                    Ok(py.detach(|| Equivalence::of(&self.0).and(&other.0).counterexample())
                            .map(<$kind as Kind>::word_out))
                }

                /// Whether no word is accepted by both DFAs.
                fn disjoint_from(&self, py: Python<'_>, other: &Self) -> PyResult<bool> {
                    crate::class::same_alphabet(self.0.ts().alphabet(), other.0.ts().alphabet())?;
                    Ok(py.detach(|| Disjointness::of(&self.0).and(&other.0).holds()))
                }

                /// The DFA for the complement language (same alphabet, accepting states swapped).
                fn complement(&self, py: Python<'_>) -> Self {
                    Self(py.detach(|| self.0.negation().reachable_part().collect_dfa()))
                }

                /// The DFA for the union of the languages (product construction, only the
                /// reachable part). The alphabets have to be equal.
                fn union(&self, py: Python<'_>, other: &Self) -> PyResult<Self> {
                    self.same_alphabet(other)?;
                    Ok(Self(py.detach(|| self.0.union(&other.0).reachable_part().collect_dfa())))
                }

                /// The DFA for the intersection of the languages, see `union`.
                fn intersection(&self, py: Python<'_>, other: &Self) -> PyResult<Self> {
                    self.same_alphabet(other)?;
                    Ok(Self(py.detach(|| self.0.intersection(&other.0).reachable_part().collect_dfa())))
                }

                /// The minimal DFA for the same language (Hopcroft).
                fn minimize(&self, py: Python<'_>) -> Self {
                    Self(py.detach(|| self.0.clone().minimize()))
                }
            }
        );

        impl $name {
            fn same_alphabet(&self, other: &Self) -> PyResult<()> {
                if self.0.ts().alphabet().size() == other.0.ts().alphabet().size() {
                    Ok(())
                } else {
                    Err(PyValueError::new_err("the automata have different alphabets"))
                }
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
            alphabet: <$front as Kind>::A,
            accepting: Vec<bool>,
            initial: Option<u32>,
            edges: Vec<Edge<$front, Void>>,
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
                symbol: <$front as Kind>::PySymbol<'_>,
                target: u32,
            ) -> PyResult<()> {
                let n = self.accepting.len();
                let edge = (
                    check_state(source, n)?,
                    <$front>::symbol(&self.alphabet, symbol)?,
                    Void,
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
                Ok($dfa(assemble::<$front, _, _>(
                    &self.alphabet,
                    self.accepting.clone(),
                    initial,
                    &self.edges,
                    automata::automaton::ReachabilityCondition,
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
