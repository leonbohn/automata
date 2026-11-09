//! Python classes for Moore machines (outputs on states) and Mealy machines (outputs on edges).

use automata::{
    DTS, Int, Void,
    alphabet::Alphabet,
    automaton::{MealySemantics, MooreSemantics},
    representation::CollectPointed,
    ts::{ForAlphabet, IntoEdgeTuple, Sproutable, TransitionSystem, q},
};
use pyo3::{exceptions::PyValueError, prelude::*};

use crate::alphabet::{PyCharAlphabet, PyPropAlphabet};
use crate::class::{Edge, assemble, automaton_class, check_state};
use crate::dfa::{PyDfa, PyPropDfa};
use crate::kind::{Chars, Kind, Props};

/// Creates a Moore machine, one state per element of `outputs`.
fn moore<K, T>(
    alphabet: &K::PyAlphabet,
    outputs: Vec<Int>,
    initial: u32,
    edges: Vec<(u32, K::PySymbol<'_>, u32)>,
) -> PyResult<automata::automaton::Automaton<T, MooreSemantics>>
where
    K: Kind,
    T: ForAlphabet<K::A> + Sproutable<Alphabet = K::A, StateColor = Int, EdgeColor = Void>,
    (
        T::StateIndex,
        <K::A as Alphabet>::Expression,
        Void,
        T::StateIndex,
    ): IntoEdgeTuple<T>,
{
    let n = outputs.len();
    let alphabet = K::alphabet(alphabet);
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
    Ok(assemble::<K, T, _>(
        &alphabet,
        outputs,
        initial,
        &edges,
        MooreSemantics,
    ))
}

/// Creates a Mealy machine with `num_states` states.
fn mealy<K, T>(
    alphabet: &K::PyAlphabet,
    num_states: u32,
    initial: u32,
    edges: Vec<(u32, K::PySymbol<'_>, Int, u32)>,
) -> PyResult<automata::automaton::Automaton<T, MealySemantics>>
where
    K: Kind,
    T: ForAlphabet<K::A> + Sproutable<Alphabet = K::A, StateColor = Void, EdgeColor = Int>,
    (
        T::StateIndex,
        <K::A as Alphabet>::Expression,
        Int,
        T::StateIndex,
    ): IntoEdgeTuple<T>,
{
    let n = num_states as usize;
    let alphabet = K::alphabet(alphabet);
    check_state(initial, n)?;
    let edges = edges
        .into_iter()
        .map(|(s, sym, o, t)| {
            Ok((
                check_state(s, n)?,
                K::symbol(&alphabet, sym)?,
                o,
                check_state(t, n)?,
            ))
        })
        .collect::<PyResult<Vec<Edge<K, Int>>>>()?;
    Ok(assemble::<K, T, _>(
        &alphabet,
        vec![Void; n],
        initial,
        &edges,
        MealySemantics,
    ))
}

macro_rules! moore_class {
    ($name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $dfa:ident, $mealy:ident, $doc:expr) => {
        automaton_class!(
            $name, $py_name, $kind, $pyalpha,
            DTS<<$kind as Kind>::A, Int, Void>, MooreSemantics,
            edge = (u32, String, u32), out = |s, l, _c: &Void, t| (s, l, t), doc = $doc,
            {
                /// The automaton in the DOT format (of graphviz).
                fn to_dot(&self) -> String {
                    ::automata::dot::Dottable::dot_representation(&self.0)
                }

                /// The automaton as an SVG image, which is how Jupyter shows it (drawn natively,
                /// graphviz is not needed).
                fn _repr_svg_(&self, py: ::pyo3::Python<'_>) -> ::pyo3::PyResult<String> {
                    $crate::class::svg(py, &self.0)
                }

                /// Creates the Moore machine with states `0, ..., len(state_colors) - 1`; state
                /// `i` outputs `state_colors[i]` (an integer from 0 to 255). `edges` are triples
                /// `(source, symbol, target)`; a later edge replaces an earlier one with the same
                /// source and symbol. Raises `ValueError` for states or symbols that do not exist.
                #[new]
                fn new(
                    alphabet: &$pyalpha,
                    state_colors: Vec<Int>,
                    initial: u32,
                    edges: Vec<(u32, <$kind as Kind>::PySymbol<'_>, u32)>,
                ) -> PyResult<Self> {
                    moore::<$kind, _>(alphabet, state_colors, initial, edges).map(Self)
                }

                /// The output of the state that the word reaches (the output of the initial state
                /// for the empty word), or `None` if the run leaves the machine (missing edge).
                fn output(
                    &self,
                    py: Python<'_>,
                    word: <$kind as Kind>::PyWord<'_>,
                ) -> PyResult<Option<Int>> {
                    let word = <$kind as Kind>::word(self.0.ts().alphabet(), word)?;
                    Ok(py.detach(|| self.0.map(word)))
                }

                /// The output of a state. Raises `IndexError` if it does not exist.
                fn state_output(&self, state: u32) -> PyResult<Int> {
                    self.edges_from(state)?;
                    Ok(self.0.ts().state_color(q(state)).map_or(0, |c| *c))
                }

                /// The outputs of the states that are reachable from the initial state, sorted
                /// and without duplicates.
                fn color_range(&self) -> Vec<u32> {
                    let mut colors: Vec<_> = self.0.color_range().into_iter().map(u32::from).collect();
                    colors.sort_unstable();
                    colors
                }

                /// For each output `c` that occurs (in increasing order) the minimal DFA that
                /// accepts exactly the words whose output is at most `c`.
                fn decompose_dfa(&self, py: Python<'_>) -> Vec<$dfa> {
                    py.detach(|| self.0.decompose_dfa()).into_iter().map($dfa).collect()
                }

                /// The minimal DFA that accepts the words whose output is at most `color`.
                fn color_or_below_dfa(&self, py: Python<'_>, color: Int) -> $dfa {
                    $dfa(py.detach(|| self.0.color_or_below_dfa(color)))
                }

                /// Whether both machines have the same output on every word. Raises
                /// `ValueError` if the alphabets differ.
                fn bisimilar(&self, py: Python<'_>, other: &Self) -> PyResult<bool> {
                    self.same_alphabet(other)?;
                    Ok(py.detach(|| self.0.bisimilar(&other.0)))
                }

                /// A word on which the outputs of the machines differ, or `None` if they are
                /// bisimilar. Raises `ValueError` if the alphabets differ.
                fn witness_non_bisimilarity(
                    &self,
                    py: Python<'_>,
                    other: &Self,
                ) -> PyResult<Option<<$kind as Kind>::PyWordOut>> {
                    self.same_alphabet(other)?;
                    Ok(py
                        .detach(|| self.0.witness_non_bisimilarity(&other.0))
                        .map(<$kind as Kind>::word_out))
                }

                /// The minimal Moore machine with the same output on every word (Hopcroft).
                fn minimize(&self, py: Python<'_>) -> Self {
                    Self(py.detach(|| self.0.minimize()))
                }

                /// The Mealy machine whose edges output the output of their source state: both
                /// produce the same sequences of outputs, except for the output of the initial
                /// state which a Mealy machine has no way to produce.
                fn push_colors_to_outgoing_edges(&self, py: Python<'_>) -> $mealy {
                    $mealy(py.detach(|| {
                        self.0
                            .push_colors_to_outgoing_edges()
                            .erase_state_colors()
                            .collect_mealy()
                    }))
                }
            }
        );

        impl $name {
            fn same_alphabet(&self, other: &Self) -> PyResult<()> {
                if self.0.ts().alphabet().size() == other.0.ts().alphabet().size() {
                    Ok(())
                } else {
                    Err(PyValueError::new_err("the machines have different alphabets"))
                }
            }
        }
    };
}

macro_rules! mealy_class {
    ($name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $doc:expr) => {
        automaton_class!(
            $name, $py_name, $kind, $pyalpha,
            DTS<<$kind as Kind>::A, Void, Int>, MealySemantics,
            edge = (u32, String, Int, u32), out = |s, l, c: &Int, t| (s, l, *c, t), doc = $doc,
            {
                /// The automaton in the DOT format (of graphviz).
                fn to_dot(&self) -> String {
                    ::automata::dot::Dottable::dot_representation(&self.0)
                }

                /// The automaton as an SVG image, which is how Jupyter shows it (drawn natively,
                /// graphviz is not needed).
                fn _repr_svg_(&self, py: ::pyo3::Python<'_>) -> ::pyo3::PyResult<String> {
                    $crate::class::svg(py, &self.0)
                }

                /// Creates the Mealy machine with states `0, ..., num_states - 1`. `edges` are
                /// tuples `(source, symbol, output, target)` with an integer output from 0 to
                /// 255; a later edge replaces an earlier one with the same source and symbol.
                /// Raises `ValueError` for states or symbols that do not exist.
                #[new]
                fn new(
                    alphabet: &$pyalpha,
                    num_states: u32,
                    initial: u32,
                    edges: Vec<(u32, <$kind as Kind>::PySymbol<'_>, Int, u32)>,
                ) -> PyResult<Self> {
                    mealy::<$kind, _>(alphabet, num_states, initial, edges).map(Self)
                }

                /// The output of the last edge that the word takes, or `None` if the word is
                /// empty (no edge is taken) or the run leaves the machine (missing edge).
                fn output(
                    &self,
                    py: Python<'_>,
                    word: <$kind as Kind>::PyWord<'_>,
                ) -> PyResult<Option<Int>> {
                    let word = <$kind as Kind>::word(self.0.ts().alphabet(), word)?;
                    Ok(py.detach(|| self.0.transform(word)))
                }

                /// The outputs of the edges that are reachable from the initial state, sorted
                /// and without duplicates.
                fn color_range(&self) -> Vec<u32> {
                    let mut colors: Vec<_> = self.0.color_range().map(u32::from).collect();
                    colors.sort_unstable();
                    colors
                }

                /// Whether both machines have the same output on every non-empty word. Raises
                /// `ValueError` if the alphabets differ.
                fn bisimilar(&self, py: Python<'_>, other: &Self) -> PyResult<bool> {
                    self.same_alphabet(other)?;
                    Ok(py.detach(|| self.0.bisimilar(&other.0)))
                }

                /// A word whose output differs in the two machines, where a missing edge in
                /// `self` or a different output counts as a difference; edges that only `other`
                /// has are ignored. `None` if there is no such word. Raises `ValueError` if the
                /// alphabets differ.
                fn witness_restricted_inequivalence(
                    &self,
                    py: Python<'_>,
                    other: &Self,
                ) -> PyResult<Option<<$kind as Kind>::PyWordOut>> {
                    self.same_alphabet(other)?;
                    Ok(py
                        .detach(|| self.0.witness_restricted_inequivalence(&other.0))
                        .map(<$kind as Kind>::word_out))
                }

                /// A word whose output differs in the two machines (this includes words that only
                /// one of them can read), or `None` if they are bisimilar. Raises `ValueError`
                /// if the alphabets differ.
                fn witness_inequivalence(
                    &self,
                    py: Python<'_>,
                    other: &Self,
                ) -> PyResult<Option<<$kind as Kind>::PyWordOut>> {
                    self.same_alphabet(other)?;
                    Ok(py
                        .detach(|| self.0.witness_inequivalence(&other.0))
                        .map(<$kind as Kind>::word_out))
                }

                /// The minimal Mealy machine with the same output on every non-empty word
                /// (Hopcroft). Unreachable states are minimized as well and kept.
                fn minimize(&self, py: Python<'_>) -> Self {
                    Self(py.detach(|| {
                        self.0.minimize().erase_state_colors().collect_mealy()
                    }))
                }
            }
        );

        impl $name {
            fn same_alphabet(&self, other: &Self) -> PyResult<()> {
                if self.0.ts().alphabet().size() == other.0.ts().alphabet().size() {
                    Ok(())
                } else {
                    Err(PyValueError::new_err("the machines have different alphabets"))
                }
            }
        }
    };
}

moore_class!(
    PyMooreMachine,
    "MooreMachine",
    Chars,
    PyCharAlphabet,
    PyDfa,
    PyMealyMachine,
    "A Moore machine over a `CharAlphabet`: every state has an integer output (0 to 255) and a word has the output of the state it reaches. Words are strings.\n\n>>> m = MooreMachine(CharAlphabet(\"ab\"), [0, 1, 2], 0, [(0, \"a\", 1), (0, \"b\", 0), (1, \"a\", 2), (1, \"b\", 0), (2, \"a\", 2), (2, \"b\", 2)])\n>>> m.output(\"\"), m.output(\"a\"), m.output(\"aab\"), m.output(\"c\")\n(0, 1, 2, None)\n>>> m.color_range()\n[0, 1, 2]\n>>> [d.accepts(\"a\") for d in m.decompose_dfa()]\n[False, True, True]"
);

moore_class!(
    PyPropMooreMachine,
    "PropMooreMachine",
    Props,
    PyPropAlphabet,
    PyPropDfa,
    PyPropMealyMachine,
    "A Moore machine over a `PropAlphabet`, see `MooreMachine`; a symbol is a sequence of booleans, a word a sequence of symbols.\n\n>>> m = PropMooreMachine(PropAlphabet([\"p\"]), [0, 1], 0, [(0, [True], 1), (0, [False], 0), (1, [True], 1), (1, [False], 0)])\n>>> m.output([[True], [True]]), m.output([[True], [False]])\n(1, 0)"
);

mealy_class!(
    PyMealyMachine,
    "MealyMachine",
    Chars,
    PyCharAlphabet,
    "A Mealy machine over a `CharAlphabet`: every edge has an integer output (0 to 255) and a word has the output of the last edge it takes. Words are strings.\n\n>>> m = MealyMachine(CharAlphabet(\"ab\"), 2, 0, [(0, \"a\", 1, 1), (0, \"b\", 0, 0), (1, \"a\", 0, 0), (1, \"b\", 1, 1)])\n>>> m.output(\"\"), m.output(\"a\"), m.output(\"ab\"), m.output(\"c\")\n(None, 1, 1, None)\n>>> m.minimize().num_states\n2"
);

mealy_class!(
    PyPropMealyMachine,
    "PropMealyMachine",
    Props,
    PyPropAlphabet,
    "A Mealy machine over a `PropAlphabet`, see `MealyMachine`; a symbol is a sequence of booleans, a word a sequence of symbols.\n\n>>> m = PropMealyMachine(PropAlphabet([\"p\"]), 1, 0, [(0, [True], 1, 0), (0, [False], 0, 0)])\n>>> m.output([[False], [True]])\n1"
);
