//! Python classes for nondeterministic automata: NFA and the omega automata NBA, NCW, NPA.

use automata::{
    NTS, Void,
    alphabet::Alphabet,
    automaton::{
        Automaton, BuchiCondition, CoBuchiCondition, Emptiness, Equivalence, Existential,
        Inclusion, MinEvenParityCondition, ReachabilityCondition,
    },
    ts::TransitionSystem,
};
use pyo3::{exceptions::PyValueError, prelude::*, types::PyType};

use crate::alphabet::{PyCharAlphabet, PyPropAlphabet};
use crate::class::automaton_class;
use crate::dfa::{PyDfa, PyPropDfa, finite};
use crate::kind::{Chars, Kind, Props, PyOmegaWord};
use crate::omega::{PyDba, PyDcw, PyDpa, PyPropDba, PyPropDcw, PyPropDpa, colored};

/// Views a deterministic automaton as a nondeterministic one with the same transitions.
fn existential<T, C>(det: &Automaton<automata::ts::Det<T>, C>) -> Automaton<T, Existential<C>>
where
    T: TransitionSystem + Clone,
    C: Clone,
{
    let (ts, initial, condition) = det.clone().into_parts();
    Automaton::from_parts_with_acceptance(ts.into_inner(), initial, Existential(condition))
}

macro_rules! nfa_class {
    ($name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $dfa:ident, $doc:expr) => {
        automaton_class!(
            $name, $py_name, $kind, $pyalpha,
            NTS<<$kind as Kind>::A, bool, Void>, Existential<ReachabilityCondition>,
            edge = (u32, String, u32), out = |s, l, _c: &Void, t| (s, l, t), doc = $doc,
            {
                /// Creates the NFA with states `0, ..., num_states - 1`. `edges` are triples
                /// `(source, symbol, target)`; several edges with the same source and symbol are
                /// allowed. Raises `ValueError` for states or symbols that do not exist.
                #[new]
                fn new(
                    alphabet: &$pyalpha,
                    num_states: u32,
                    initial: u32,
                    accepting: Vec<u32>,
                    edges: Vec<(u32, <$kind as Kind>::PySymbol<'_>, u32)>,
                ) -> PyResult<Self> {
                    finite::<$kind, _, _>(
                        alphabet, num_states, initial, accepting, edges,
                        Existential(ReachabilityCondition),
                    )
                    .map(Self)
                }

                /// The NFA with the transitions of the DFA.
                #[classmethod]
                fn from_dfa(_cls: &Bound<'_, PyType>, dfa: &$dfa) -> Self {
                    Self(existential(&dfa.0))
                }

                /// Whether some run on the word ends in an accepting state.
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
                    Ok(self.0.ts().state_color(automata::ts::q(state)).is_some_and(|c| *c))
                }

                /// The accepting states.
                fn accepting_states(&self) -> Vec<u32> {
                    use automata::ts::States;
                    self.0
                        .ts()
                        .states()
                        .filter(|&q| self.0.ts().state_color(q).is_some_and(|c| *c))
                        .map(u32::from)
                        .collect()
                }

                /// Whether the language is empty.
                fn is_empty(&self, py: Python<'_>) -> bool {
                    py.detach(|| Emptiness::of(&self.0).holds())
                }

                /// A shortest accepted word, or `None` if the language is empty.
                fn accepting_word(&self, py: Python<'_>) -> Option<<$kind as Kind>::PyWordOut> {
                    py.detach(|| Emptiness::of(&self.0).witness()).map(<$kind as Kind>::word_out)
                }

                /// Whether the language of `self` is contained in the one of `other` (both are
                /// determinized). The alphabets have to be equal.
                fn included_in(&self, py: Python<'_>, other: &Self) -> PyResult<bool> {
                    self.same_alphabet(other)?;
                    Ok(py.detach(|| Inclusion::of(&self.0).within(&other.0).holds()))
                }

                /// A word accepted by `self` but not by `other`, or `None` if `self` is included
                /// in `other`.
                fn inclusion_counterexample(
                    &self,
                    py: Python<'_>,
                    other: &Self,
                ) -> PyResult<Option<<$kind as Kind>::PyWordOut>> {
                    self.same_alphabet(other)?;
                    Ok(py
                        .detach(|| Inclusion::of(&self.0).within(&other.0).counterexample())
                        .map(<$kind as Kind>::word_out))
                }

                /// Whether both NFAs accept the same language.
                fn equivalent_to(&self, py: Python<'_>, other: &Self) -> PyResult<bool> {
                    self.same_alphabet(other)?;
                    Ok(py.detach(|| Equivalence::of(&self.0).and(&other.0).holds()))
                }

                /// A word that exactly one of the NFAs accepts, or `None` if they are equivalent.
                fn equivalence_counterexample(
                    &self,
                    py: Python<'_>,
                    other: &Self,
                ) -> PyResult<Option<<$kind as Kind>::PyWordOut>> {
                    self.same_alphabet(other)?;
                    Ok(py
                        .detach(|| Equivalence::of(&self.0).and(&other.0).counterexample())
                        .map(<$kind as Kind>::word_out))
                }

                /// An equivalent complete `DFA` (subset construction, not minimized).
                fn determinize(&self, py: Python<'_>) -> $dfa {
                    $dfa(py.detach(|| self.0.determinize()))
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

nfa_class!(
    PyNfa,
    "NFA",
    Chars,
    PyCharAlphabet,
    PyDfa,
    "A nondeterministic finite automaton over a `CharAlphabet`; words are strings. A word is accepted if some run on it ends in an accepting state.\n\n>>> a = CharAlphabet(\"ab\")\n>>> second_last_a = NFA(a, 3, 0, [2], [(0, \"a\", 0), (0, \"b\", 0), (0, \"a\", 1), (1, \"a\", 2), (1, \"b\", 2)])\n>>> second_last_a.accepts(\"bab\")\nTrue\n>>> second_last_a.accepts(\"abb\")\nFalse\n>>> second_last_a.accepting_word()\n'aa'\n>>> dfa = second_last_a.determinize()\n>>> dfa.accepts(\"bab\"), dfa.minimize().num_states\n(True, 4)\n>>> NFA.from_dfa(dfa).equivalent_to(second_last_a)\nTrue"
);

nfa_class!(
    PyPropNfa,
    "PropNFA",
    Props,
    PyPropAlphabet,
    PyPropDfa,
    "A nondeterministic finite automaton over a `PropAlphabet`, see `NFA`; symbols are sequences of booleans.\n\n>>> a = PropAlphabet([\"p\"])\n>>> n = PropNFA(a, 2, 0, [1], [(0, [True], 0), (0, [False], 0), (0, [True], 1)])\n>>> n.accepts([[False], [True]])\nTrue\n>>> n.accepts([[True], [False]])\nFalse"
);

/// Defines a nondeterministic omega automaton class with the acceptance condition `$cond` (the
/// Büchi, co-Büchi or parity condition); `more` are further methods.
macro_rules! nomega_class {
    (
        $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $color:ty, $cond:ident, $doc:expr,
        { $($more:tt)* }
    ) => {
        automaton_class!(
            $name, $py_name, $kind, $pyalpha,
            NTS<<$kind as Kind>::A, Void, $color>, Existential<$cond>,
            edge = (u32, String, $color, u32), out = |s, l, c: &$color, t| (s, l, c.clone(), t),
            doc = $doc,
            {
                /// Creates the automaton with states `0, ..., num_states - 1`. `edges` are tuples
                /// `(source, symbol, color, target)`; several edges with the same source and
                /// symbol are allowed. Raises `ValueError` for states or symbols that do not
                /// exist.
                #[new]
                fn new(
                    alphabet: &$pyalpha,
                    num_states: u32,
                    initial: u32,
                    edges: Vec<(u32, <$kind as Kind>::PySymbol<'_>, $color, u32)>,
                ) -> PyResult<Self> {
                    colored::<$kind, _, _>(alphabet, num_states, initial, edges, Existential($cond))
                        .map(Self)
                }

                /// Whether some run on the ultimately periodic word is accepting.
                fn accepts(&self, py: Python<'_>, word: &PyOmegaWord) -> PyResult<bool> {
                    let word = <$kind as Kind>::omega(self.0.ts().alphabet(), word)?;
                    Ok(py.detach(|| self.0.accepts(word)))
                }

                /// Whether the language is empty.
                fn is_empty(&self, py: Python<'_>) -> bool {
                    py.detach(|| Emptiness::of(&self.0).holds())
                }

                /// An accepted word, or `None` if the language is empty.
                fn accepting_word(&self, py: Python<'_>) -> Option<PyOmegaWord> {
                    py.detach(|| Emptiness::of(&self.0).witness())
                        .map(|w| <$kind as Kind>::omega_out(&w))
                }

                $($more)*
            }
        );
    };
}

nomega_class!(
    PyNba,
    "NBA",
    Chars,
    PyCharAlphabet,
    bool,
    BuchiCondition,
    "A nondeterministic Büchi automaton over a `CharAlphabet`. An infinite word is accepted if some run uses edges with color `True` infinitely often.\n\n>>> a = CharAlphabet(\"ab\")\n>>> finitely_many_a = NBA(a, 2, 0, [(0, \"a\", False, 0), (0, \"b\", False, 0), (0, \"b\", False, 1), (1, \"b\", True, 1)])\n>>> finitely_many_a.accepts(OmegaWord(\"ab\", \"b\"))\nTrue\n>>> finitely_many_a.accepts(OmegaWord(\"\", \"ab\"))\nFalse\n>>> finitely_many_a.accepting_word() is not None\nTrue",
    {
        /// The NBA with the transitions of the DBA.
        #[classmethod]
        fn from_dba(_cls: &Bound<'_, PyType>, dba: &PyDba) -> Self {
            Self(existential(&dba.0))
        }

        /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
        fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::to_hoa(py, &self.0)
        }
    }
);
nomega_class!(
    PyPropNba,
    "PropNBA",
    Props,
    PyPropAlphabet,
    bool,
    BuchiCondition,
    "A nondeterministic Büchi automaton over a `PropAlphabet`, see `NBA`.",
    {
        /// The PropNBA with the transitions of the PropDBA.
        #[classmethod]
        fn from_dba(_cls: &Bound<'_, PyType>, dba: &PyPropDba) -> Self {
            Self(existential(&dba.0))
        }

        /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
        fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::to_hoa(py, &self.0)
        }

        /// Reads the first automaton in the HOA text, which may be deterministic. Raises `HoaError` if its acceptance
        /// condition is not Büchi.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::nba(py, text).map(Self)
        }
    }
);

nomega_class!(
    PyNcw,
    "NCW",
    Chars,
    PyCharAlphabet,
    bool,
    CoBuchiCondition,
    "A nondeterministic co-Büchi automaton over a `CharAlphabet`. An infinite word is accepted if some run uses edges with color `True` only finitely often.\n\n>>> a = CharAlphabet(\"ab\")\n>>> finitely_many_a = NCW(a, 2, 0, [(0, \"a\", True, 0), (0, \"b\", True, 0), (0, \"b\", False, 1), (1, \"b\", False, 1)])\n>>> finitely_many_a.accepts(OmegaWord(\"ab\", \"b\"))\nTrue\n>>> finitely_many_a.accepts(OmegaWord(\"\", \"ab\"))\nFalse",
    {
        /// The NCW with the transitions of the DCW.
        #[classmethod]
        fn from_dcw(_cls: &Bound<'_, PyType>, dcw: &PyDcw) -> Self {
            Self(existential(&dcw.0))
        }
    }
);
nomega_class!(
    PyPropNcw,
    "PropNCW",
    Props,
    PyPropAlphabet,
    bool,
    CoBuchiCondition,
    "A nondeterministic co-Büchi automaton over a `PropAlphabet`, see `NCW`.",
    {
        /// The PropNCW with the transitions of the PropDCW.
        #[classmethod]
        fn from_dcw(_cls: &Bound<'_, PyType>, dcw: &PyPropDcw) -> Self {
            Self(existential(&dcw.0))
        }
    }
);

nomega_class!(
    PyNpa,
    "NPA",
    Chars,
    PyCharAlphabet,
    u8,
    MinEvenParityCondition,
    "A nondeterministic parity automaton over a `CharAlphabet` (min-even): an infinite word is accepted if some run has an even smallest color among those seen infinitely often. Colors are integers from 0 to 255.\n\n>>> a = CharAlphabet(\"ab\")\n>>> finitely_many_a = NPA(a, 2, 0, [(0, \"a\", 1, 0), (0, \"b\", 1, 0), (0, \"b\", 1, 1), (1, \"b\", 0, 1)])\n>>> finitely_many_a.accepts(OmegaWord(\"ab\", \"b\"))\nTrue\n>>> finitely_many_a.accepts(OmegaWord(\"\", \"ab\"))\nFalse",
    {
        /// The NPA with the transitions of the DPA.
        #[classmethod]
        fn from_dpa(_cls: &Bound<'_, PyType>, dpa: &PyDpa) -> Self {
            Self(existential(&dpa.0))
        }

        /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
        fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::to_hoa(py, &self.0)
        }
    }
);
nomega_class!(
    PyPropNpa,
    "PropNPA",
    Props,
    PyPropAlphabet,
    u8,
    MinEvenParityCondition,
    "A nondeterministic parity automaton over a `PropAlphabet`, see `NPA`.",
    {
        /// The PropNPA with the transitions of the PropDPA.
        #[classmethod]
        fn from_dpa(_cls: &Bound<'_, PyType>, dpa: &PyPropDpa) -> Self {
            Self(existential(&dpa.0))
        }

        /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
        fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::to_hoa(py, &self.0)
        }

        /// Reads the first automaton in the HOA text, which may be deterministic. Only min parity conditions are
        /// supported. Raises `HoaError` for other conditions and `NotImplementedError` for max parity.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::npa(py, text).map(Self)
        }
    }
);
