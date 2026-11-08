//! Python classes for deterministic omega automata with a fixed acceptance condition.

use automata::{
    DTS, Int, Void,
    alphabet::Alphabet,
    automaton::{
        Automaton, BuchiCondition, CoBuchiCondition, Emptiness, Equivalence, Inclusion,
        MinEvenParityCondition, MullerCondition, RabinCondition, RabinPair,
    },
    ts::{ForAlphabet, IntoEdgeTuple, Sproutable, TransitionSystem},
};
use pyo3::{exceptions::PyValueError, prelude::*};

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
        omega_class!($name, $py_name, $kind, $pyalpha, $color, $sem, $doc, plain, {
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
        omega_class!(@inner $name, $py_name, $kind, $pyalpha, $color, $sem, $doc, {
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

            $($more)*
        });
    };
    // like `plain`, but `more` has to contain the constructor (for conditions that carry data)
    (
        $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $color:ty, $sem:ty, $doc:expr,
        custom_new, { $($more:tt)* }
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

omega_class!(
    PyDcw,
    "DCW",
    Chars,
    PyCharAlphabet,
    bool,
    CoBuchiCondition,
    "A deterministic co-Büchi automaton over a `CharAlphabet`. An infinite word is accepted if its run uses edges with color `True` only finitely often.\n\n>>> a = CharAlphabet(\"ab\")\n>>> fin_a = DCW(a, 1, 0, [(0, \"a\", True, 0), (0, \"b\", False, 0)])\n>>> fin_a.accepts(OmegaWord(\"aa\", \"b\"))\nTrue\n>>> fin_a.accepts(OmegaWord(\"\", \"ab\"))\nFalse\n>>> fin_a.is_empty()\nFalse",
    plain,
    {}
);
omega_class!(
    PyPropDcw,
    "PropDCW",
    Props,
    PyPropAlphabet,
    bool,
    CoBuchiCondition,
    "A deterministic co-Büchi automaton over a `PropAlphabet`, see `DCW`.",
    plain,
    {}
);

/// Defines a deterministic parity automaton class (min-even: a word is accepted if the least
/// color its run uses infinitely often is even), which has the extra methods of `DPA` of the
/// crate.
macro_rules! dpa_class {
    ($name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $doc:expr) => {
        omega_class!(
            $name,
            $py_name,
            $kind,
            $pyalpha,
            Int,
            MinEvenParityCondition,
            $doc,
            comparisons,
            {
                /// The complement: an automaton that accepts exactly the words that `self`
                /// rejects. The automaton is expected to be complete. Raises `ValueError` if
                /// the colors of the result do not fit into `0..=255`.
                fn complement(&self, py: Python<'_>) -> PyResult<Self> {
                    py.detach(|| self.0.normalized().complement_without_normalizing())
                        .map(Self)
                        .ok_or_else(|| {
                            PyValueError::new_err("the complement needs more than 256 colors")
                        })
                }

                /// An equivalent automaton that uses as few different colors as possible.
                fn normalized(&self, py: Python<'_>) -> Self {
                    Self(py.detach(|| self.0.normalized()))
                }

                /// An equivalent automaton with few colors and merged equivalent states.
                fn streamlined(&self, py: Python<'_>) -> Self {
                    Self(py.detach(|| self.0.streamlined()))
                }

                /// A word that is rejected, or `None` if the language is universal.
                fn rejected_word(&self, py: Python<'_>) -> Option<PyOmegaWord> {
                    py.detach(|| self.0.give_rejected_word())
                        .map(|w| <$kind as Kind>::omega_out(&w))
                }
            }
        );
    };
}

dpa_class!(
    PyDpa,
    "DPA",
    Chars,
    PyCharAlphabet,
    "A deterministic parity automaton over a `CharAlphabet` with colors `0..=255` on the edges (others raise `OverflowError`) (min-even: a word is accepted if the least color that its run uses infinitely often is even; the other parity conditions are not available).\n\n>>> a = CharAlphabet(\"ab\")\n>>> inf_b = DPA(a, 1, 0, [(0, \"a\", 1, 0), (0, \"b\", 0, 0)])\n>>> inf_b.accepts(OmegaWord(\"a\", \"ab\"))\nTrue\n>>> inf_b.accepts(OmegaWord(\"b\", \"a\"))\nFalse\n>>> inf_b.complement().accepts(OmegaWord(\"b\", \"a\"))\nTrue\n>>> inf_b.complement().complement().equivalent_to(inf_b)\nTrue\n>>> inf_b.rejected_word() is not None\nTrue"
);
dpa_class!(
    PyPropDpa,
    "PropDPA",
    Props,
    PyPropAlphabet,
    "A deterministic parity automaton over a `PropAlphabet`, see `DPA`."
);

/// Defines a deterministic Rabin automaton class, whose constructor takes a list of pairs
/// `(fin, inf)` of lists of colors.
macro_rules! dra_class {
    ($name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $doc:expr) => {
        omega_class!(
            $name,
            $py_name,
            $kind,
            $pyalpha,
            Int,
            RabinCondition<Int>,
            $doc,
            custom_new,
            {
                /// Creates the automaton with states `0, ..., num_states - 1`. `edges` are
                /// tuples `(source, symbol, color, target)`; a later edge replaces an earlier
                /// one with the same source and symbol. `pairs` is a list of `(fin, inf)`
                /// where both are lists of colors. Raises `ValueError` for states or symbols
                /// that do not exist.
                #[new]
                fn new(
                    alphabet: &$pyalpha,
                    num_states: u32,
                    initial: u32,
                    edges: Vec<(u32, <$kind as Kind>::PySymbol<'_>, Int, u32)>,
                    pairs: Vec<(Vec<Int>, Vec<Int>)>,
                ) -> PyResult<Self> {
                    let condition: RabinCondition<Int> = pairs
                        .into_iter()
                        .map(|(fin, inf)| RabinPair::from_iters(fin, inf))
                        .into();
                    colored::<$kind, _, _>(alphabet, num_states, initial, edges, condition)
                        .map(Self)
                }
            }
        );
    };
}

dra_class!(
    PyDra,
    "DRA",
    Chars,
    PyCharAlphabet,
    "A deterministic Rabin automaton over a `CharAlphabet` with colors `0..=255` on the edges (others raise `OverflowError`). A word is accepted if for some pair `(fin, inf)` its run uses no color of `fin` and some color of `inf` infinitely often.\n\n>>> a = CharAlphabet(\"ab\")\n>>> edges = [(0, \"a\", 0, 0), (0, \"b\", 1, 1), (1, \"a\", 0, 0), (1, \"b\", 1, 1)]\n>>> inf_b = DRA(a, 2, 0, edges, [([], [1])])\n>>> inf_b.accepts(OmegaWord(\"\", \"ba\"))\nTrue\n>>> inf_b.accepts(OmegaWord(\"b\", \"a\"))\nFalse\n>>> inf_b.is_empty()\nFalse"
);
dra_class!(
    PyPropDra,
    "PropDRA",
    Props,
    PyPropAlphabet,
    "A deterministic Rabin automaton over a `PropAlphabet`, see `DRA`."
);

/// Defines a deterministic Muller automaton class, whose constructor takes a list of sets
/// (lists) of colors.
macro_rules! dma_class {
    ($name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $doc:expr) => {
        omega_class!(
            $name,
            $py_name,
            $kind,
            $pyalpha,
            Int,
            MullerCondition<Int>,
            $doc,
            custom_new,
            {
                /// Creates the automaton with states `0, ..., num_states - 1`. `edges` are
                /// tuples `(source, symbol, color, target)`; a later edge replaces an earlier
                /// one with the same source and symbol. `sets` is a list of lists of colors:
                /// a word is accepted if the colors that its run uses infinitely often are
                /// exactly one of the lists. Raises `ValueError` for states or symbols that
                /// do not exist.
                #[new]
                fn new(
                    alphabet: &$pyalpha,
                    num_states: u32,
                    initial: u32,
                    edges: Vec<(u32, <$kind as Kind>::PySymbol<'_>, Int, u32)>,
                    sets: Vec<Vec<Int>>,
                ) -> PyResult<Self> {
                    colored::<$kind, _, _>(
                        alphabet,
                        num_states,
                        initial,
                        edges,
                        MullerCondition::from_iter_iter(sets),
                    )
                    .map(Self)
                }
            }
        );
    };
}

dma_class!(
    PyDma,
    "DMA",
    Chars,
    PyCharAlphabet,
    "A deterministic Muller automaton over a `CharAlphabet` with colors `0..=255` on the edges (others raise `OverflowError`). A word is accepted if the set of colors that its run uses infinitely often is one of the given sets.\n\n>>> a = CharAlphabet(\"ab\")\n>>> edges = [(0, \"a\", 0, 0), (0, \"b\", 1, 1), (1, \"a\", 0, 0), (1, \"b\", 1, 1)]\n>>> only_one = DMA(a, 2, 0, edges, [[0], [1]])\n>>> only_one.accepts(OmegaWord(\"\", \"a\"))\nTrue\n>>> only_one.accepts(OmegaWord(\"\", \"ba\"))\nFalse\n>>> only_one.is_empty()\nFalse"
);
dma_class!(
    PyPropDma,
    "PropDMA",
    Props,
    PyPropAlphabet,
    "A deterministic Muller automaton over a `PropAlphabet`, see `DMA`."
);
