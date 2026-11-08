//! Python classes for deterministic omega automata with a fixed acceptance condition.

use automata::{
    DTS, Void,
    alphabet::Alphabet,
    automaton::{Automaton, BuchiCondition, Emptiness, Equivalence, Inclusion},
    ts::{ForAlphabet, IntoEdgeTuple, Sproutable, TransitionSystem},
};
use pyo3::prelude::*;

use crate::alphabet::{PyCharAlphabet, PyPropAlphabet};
use crate::class::{Edge, assemble, automaton_class, check_state};
use crate::kind::{Chars, Kind, Props, PyOmegaWord};

/// Creates an omega automaton whose states are uncolored and whose edges carry colors.
pub fn colored<K, T, Sem>(
    alphabet: &K::PyAlphabet,
    num_states: u32,
    initial: u32,
    edges: Vec<(u32, K::PySymbol<'_>, T::EdgeColor, u32)>,
    semantics: Sem,
) -> PyResult<Automaton<T, Sem>>
where
    K: Kind,
    T: ForAlphabet<K::A> + Sproutable<Alphabet = K::A, StateColor = Void>,
    T::EdgeColor: Clone,
    (
        T::StateIndex,
        <K::A as Alphabet>::Expression,
        T::EdgeColor,
        T::StateIndex,
    ): IntoEdgeTuple<T>,
{
    let n = num_states as usize;
    let alphabet = K::alphabet(alphabet);
    check_state(initial, n)?;
    let edges = edges
        .into_iter()
        .map(|(s, sym, c, t)| {
            Ok((
                check_state(s, n)?,
                K::symbol(&alphabet, sym)?,
                c,
                check_state(t, n)?,
            ))
        })
        .collect::<PyResult<Vec<Edge<K, T::EdgeColor>>>>()?;
    Ok(assemble::<K, T, Sem>(
        &alphabet,
        vec![Void; n],
        initial,
        &edges,
        semantics,
    ))
}

/// Defines an omega automaton class, `omega_class!(..., comparisons, { more })` for the classes
/// whose inclusion and equivalence the crate can decide and `omega_class!(..., plain, { more })`
/// for the others. `more` are further methods.
macro_rules! omega_class {
    (
        $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $color:ty, $sem:ty, $doc:expr,
        comparisons, { $($more:tt)* }
    ) => {
        omega_class!(@inner $name, $py_name, $kind, $pyalpha, $color, $sem, $doc, {
            /// Whether the language of `self` is contained in the one of `other`.
            fn included_in(&self, py: Python<'_>, other: &Self) -> bool {
                py.detach(|| Inclusion::of(&self.0).within(&other.0).holds())
            }

            /// A word accepted by `self` but not by `other`, or `None` if `self` is included in
            /// `other`.
            fn inclusion_counterexample(&self, py: Python<'_>, other: &Self) -> Option<PyOmegaWord> {
                py.detach(|| Inclusion::of(&self.0).within(&other.0).counterexample())
                    .map(|w| <$kind as Kind>::omega_out(&w))
            }

            /// Whether both automata accept the same language.
            fn equivalent_to(&self, py: Python<'_>, other: &Self) -> bool {
                py.detach(|| Equivalence::of(&self.0).and(&other.0).holds())
            }

            /// A word that exactly one of the automata accepts, or `None` if they are equivalent.
            fn equivalence_counterexample(&self, py: Python<'_>, other: &Self) -> Option<PyOmegaWord> {
                py.detach(|| Equivalence::of(&self.0).and(&other.0).counterexample())
                    .map(|w| <$kind as Kind>::omega_out(&w))
            }

            $($more)*
        });
    };
    (
        $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $color:ty, $sem:ty, $doc:expr,
        plain, { $($more:tt)* }
    ) => {
        omega_class!(@inner $name, $py_name, $kind, $pyalpha, $color, $sem, $doc, { $($more)* });
    };
    (
        @inner $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $color:ty, $sem:ty, $doc:expr,
        { $($more:tt)* }
    ) => {
        automaton_class!(
            $name, $py_name, $kind, $pyalpha,
            DTS<<$kind as Kind>::A, Void, $color>, $sem,
            edge = (u32, String, $color, u32), out = |s, l, c: &$color, t| (s, l, c.clone(), t),
            doc = $doc,
            {
                /// Creates the automaton with states `0, ..., num_states - 1`. `edges` are tuples
                /// `(source, symbol, color, target)`; a later edge replaces an earlier one with
                /// the same source and symbol. Raises `ValueError` for states or symbols that
                /// do not exist.
                #[new]
                fn new(
                    alphabet: &$pyalpha,
                    num_states: u32,
                    initial: u32,
                    edges: Vec<(u32, <$kind as Kind>::PySymbol<'_>, $color, u32)>,
                ) -> PyResult<Self> {
                    colored::<$kind, _, _>(alphabet, num_states, initial, edges, Default::default())
                        .map(Self)
                }

                /// Whether the automaton accepts the ultimately periodic word.
                fn accepts(&self, py: Python<'_>, word: &PyOmegaWord) -> PyResult<bool> {
                    let word = <$kind as Kind>::omega(self.0.ts().alphabet(), word)?;
                    Ok(py.detach(|| self.0.accepts(word)))
                }

                /// Whether the language is empty. The automaton is expected to be complete.
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

omega_class!(
    PyDba,
    "DBA",
    Chars,
    PyCharAlphabet,
    bool,
    BuchiCondition,
    "A deterministic Büchi automaton over a `CharAlphabet`. An infinite word is accepted if its run uses edges with color `True` infinitely often.\n\n>>> a = CharAlphabet(\"ab\")\n>>> inf_a = DBA(a, 1, 0, [(0, \"a\", True, 0), (0, \"b\", False, 0)])\n>>> inf_a.accepts(OmegaWord(\"b\", \"ab\"))\nTrue\n>>> inf_a.accepts(OmegaWord(\"a\", \"b\"))\nFalse\n>>> inf_a.is_empty()\nFalse",
    comparisons,
    {}
);
omega_class!(
    PyPropDba,
    "PropDBA",
    Props,
    PyPropAlphabet,
    bool,
    BuchiCondition,
    "A deterministic Büchi automaton over a `PropAlphabet`, see `DBA`.",
    comparisons,
    {}
);
