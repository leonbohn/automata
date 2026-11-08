//! Python classes for deterministic omega automata with a fixed acceptance condition.

use automata::{
    DTS, Int, Void,
    alphabet::Alphabet,
    automaton::{
        Automaton, BuchiCondition, CoBuchiCondition, Emptiness, Equivalence, Inclusion,
        MaxEvenParityCondition, MaxOddParityCondition, MinEvenParityCondition,
        MinOddParityCondition, MullerCondition, ParityKind, RabinCondition, RabinPair,
        StreettCondition,
    },
    representation::IntoTransitions,
    ts::{ForAlphabet, IntoEdgeTuple, Sproutable, States, TransitionSystem},
};
use pyo3::{exceptions::PyValueError, prelude::*, types::PyType};

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

/// The DPA with the same transitions as `det`, whose edge color `c` becomes `color(c)`. For a
/// Büchi automaton, `color` maps `true` below `false` (as `into_dpa` of the crate does), for a
/// co-Büchi automaton `true` has to be odd and `false` even and larger.
fn parity_of<A: Alphabet, Sem: Clone>(
    det: &Automaton<DTS<A, Void, bool>, Sem>,
    color: impl Fn(bool) -> Int,
) -> Automaton<DTS<A, Void, Int>, MinEvenParityCondition> {
    let (ts, initial, _) = det.clone().into_parts();
    ts.map_edge_colors(color).with_initial(initial).collect()
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
            fn included_in(&self, py: Python<'_>, other: &Self) -> PyResult<bool> {
                crate::class::same_alphabet(self.0.ts().alphabet(), other.0.ts().alphabet())?;
                Ok(py.detach(|| Inclusion::of(&self.0).within(&other.0).holds()))
            }

            /// A word accepted by `self` but not by `other`, or `None` if `self` is included in
            /// `other`.
            fn inclusion_counterexample(&self, py: Python<'_>, other: &Self) -> PyResult<Option<PyOmegaWord>> {
                crate::class::same_alphabet(self.0.ts().alphabet(), other.0.ts().alphabet())?;
                Ok(py.detach(|| Inclusion::of(&self.0).within(&other.0).counterexample())
                        .map(|w| <$kind as Kind>::omega_out(&w)))
            }

            /// Whether both automata accept the same language.
            fn equivalent_to(&self, py: Python<'_>, other: &Self) -> PyResult<bool> {
                crate::class::same_alphabet(self.0.ts().alphabet(), other.0.ts().alphabet())?;
                Ok(py.detach(|| Equivalence::of(&self.0).and(&other.0).holds()))
            }

            /// A word that exactly one of the automata accepts, or `None` if they are equivalent.
            fn equivalence_counterexample(&self, py: Python<'_>, other: &Self) -> PyResult<Option<PyOmegaWord>> {
                crate::class::same_alphabet(self.0.ts().alphabet(), other.0.ts().alphabet())?;
                Ok(py.detach(|| Equivalence::of(&self.0).and(&other.0).counterexample())
                        .map(|w| <$kind as Kind>::omega_out(&w)))
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
    // like `custom_new`, but without `is_empty` and `accepting_word` (for the conditions that the
    // crate has no emptiness check for, `more` has to provide them)
    (
        $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $color:ty, $sem:ty, $doc:expr,
        no_emptiness, { $($more:tt)* }
    ) => {
        omega_class!(@base $name, $py_name, $kind, $pyalpha, $color, $sem, $doc, { $($more)* });
    };
    (
        @inner $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $color:ty, $sem:ty, $doc:expr,
        { $($more:tt)* }
    ) => {
        omega_class!(@base $name, $py_name, $kind, $pyalpha, $color, $sem, $doc, {
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
        });
    };
    (
        @base $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $color:ty, $sem:ty, $doc:expr,
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
    "A deterministic Büchi automaton over a `CharAlphabet`. An infinite word is accepted if its run uses edges with color `True` infinitely often.\n\n>>> a = CharAlphabet(\"ab\")\n>>> inf_a = DBA(a, 1, 0, [(0, \"a\", True, 0), (0, \"b\", False, 0)])\n>>> inf_a.accepts(OmegaWord(\"b\", \"ab\"))\nTrue\n>>> inf_a.accepts(OmegaWord(\"a\", \"b\"))\nFalse\n>>> inf_a.is_empty()\nFalse\n\nThe HOA format writes the characters as propositions and reads them back as a `PropDBA`.\n\n>>> hoa = inf_a.to_hoa()\n>>> hoa.splitlines()[0]\n'HOA: v1'\n>>> PropDBA.from_hoa(hoa).num_edges\n2\n>>> type(parse_hoa(hoa)).__name__\n'PropDBA'\n>>> inf_a.to_dot().startswith(\"digraph\")\nTrue",
    comparisons,
    {
        /// The automaton in the DOT format (of graphviz).
        fn to_dot(&self) -> String {
            automata::dot::Dottable::dot_representation(&self.0)
        }

        /// The automaton as an SVG image, which is how Jupyter shows it (drawn natively, graphviz is
        /// not needed).
        fn _repr_svg_(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::svg(py, &self.0)
        }

        /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
        fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::to_hoa(py, &self.0)
        }
    }
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
    {
        /// The automaton in the DOT format (of graphviz).
        fn to_dot(&self) -> String {
            automata::dot::Dottable::dot_representation(&self.0)
        }

        /// The automaton as an SVG image, which is how Jupyter shows it (drawn natively, graphviz is
        /// not needed).
        fn _repr_svg_(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::svg(py, &self.0)
        }

        /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
        fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::to_hoa(py, &self.0)
        }

        /// Reads the first automaton in the HOA text. Raises `HoaError` if the text is not a
        /// (supported) deterministic Büchi automaton.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::dba(py, text).map(Self)
        }
    }
);

omega_class!(
    PyDcw,
    "DCW",
    Chars,
    PyCharAlphabet,
    bool,
    CoBuchiCondition,
    "A deterministic co-Büchi automaton over a `CharAlphabet`. An infinite word is accepted if its run uses edges with color `True` only finitely often.\n\n>>> a = CharAlphabet(\"ab\")\n>>> fin_a = DCW(a, 1, 0, [(0, \"a\", True, 0), (0, \"b\", False, 0)])\n>>> fin_a.accepts(OmegaWord(\"aa\", \"b\"))\nTrue\n>>> fin_a.accepts(OmegaWord(\"\", \"ab\"))\nFalse\n>>> fin_a.is_empty()\nFalse\n\nThe HOA format writes the characters as propositions and reads them back as a `PropDCW`.\n\n>>> PropDCW.from_hoa(fin_a.to_hoa()).num_edges\n2\n>>> type(parse_hoa(fin_a.to_hoa())).__name__\n'PropDCW'",
    plain,
    {
        /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
        fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::to_hoa(py, &self.0)
        }
    }
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
    {
        /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
        fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
            crate::class::to_hoa(py, &self.0)
        }

        /// Reads the first automaton in the HOA text. Raises `HoaError` if the text is not a
        /// (supported) deterministic co-Büchi automaton.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::dcw(py, text).map(Self)
        }
    }
);

/// Defines a deterministic parity automaton class (min-even: a word is accepted if the least
/// color its run uses infinitely often is even), which has the extra methods of `DPA` of the
/// crate.
macro_rules! dpa_class {
    ($name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $dba:ident, $dcw:ident, $doc:expr, { $($more:tt)* }) => {
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
                /// The automaton in the DOT format (of graphviz).
                fn to_dot(&self) -> String {
                    ::automata::dot::Dottable::dot_representation(&self.0)
                }

                /// The automaton as an SVG image, which is how Jupyter shows it (drawn natively,
                /// graphviz is not needed).
                fn _repr_svg_(&self, py: ::pyo3::Python<'_>) -> ::pyo3::PyResult<String> {
                    $crate::class::svg(py, &self.0)
                }

                /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
                fn to_hoa(&self, py: ::pyo3::Python<'_>) -> ::pyo3::PyResult<String> {
                    $crate::class::to_hoa(py, &self.0)
                }

/// The DPA with the colors `0` and `1` for the edges of the DBA with color `True` and
                /// `False`, which accepts the same language.
                #[classmethod]
                fn from_dba(_cls: &Bound<'_, PyType>, dba: &$dba) -> Self {
                    Self(parity_of(&dba.0, |accepting| Int::from(!accepting)))
                }

                /// The DPA with the colors `1` and `2` for the edges of the DCW with color `True`
                /// and `False`, which accepts the same language.
                #[classmethod]
                fn from_dcw(_cls: &Bound<'_, PyType>, dcw: &$dcw) -> Self {
                    Self(parity_of(&dcw.0, |bad| if bad { 1 } else { 2 }))
                }

                $($more)*

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
    PyDba,
    PyDcw,
    "A deterministic parity automaton over a `CharAlphabet` with colors `0..=255` on the edges (others raise `OverflowError`) (min-even: a word is accepted if the least color that its run uses infinitely often is even; the other parity conditions are the classes `DPAMaxEven`, `DPAMinOdd` and `DPAMaxOdd`).\n\n>>> a = CharAlphabet(\"ab\")\n>>> inf_b = DPA(a, 1, 0, [(0, \"a\", 1, 0), (0, \"b\", 0, 0)])\n>>> inf_b.accepts(OmegaWord(\"a\", \"ab\"))\nTrue\n>>> inf_b.accepts(OmegaWord(\"b\", \"a\"))\nFalse\n>>> inf_b.complement().accepts(OmegaWord(\"b\", \"a\"))\nTrue\n>>> inf_b.complement().complement().equivalent_to(inf_b)\nTrue\n>>> inf_b.rejected_word() is not None\nTrue",
    {}
);
dpa_class!(
    PyPropDpa,
    "PropDPA",
    Props,
    PyPropAlphabet,
    PyPropDba,
    PyPropDcw,
    "A deterministic parity automaton over a `PropAlphabet`, see `DPA`.",
    {
        /// Reads the first automaton in the HOA text and converts it to a min-even DPA: every
        /// parity kind (`min even`, `min odd`, `max even`, `max odd`), Büchi and co-Büchi are
        /// accepted, the colors are renumbered as `to_min_even` of the variant classes does.
        /// Raises `HoaError` if the text is not a (supported) deterministic automaton with one of
        /// these conditions and `NotImplementedError` for Rabin and Streett conditions. Use the
        /// variant classes (e.g. `PropDPAMaxEven.from_hoa`) to keep the colors.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::dpa(py, text).map(Self)
        }
    }
);

/// A min-even DPA that accepts the language of `aut`, an automaton with the parity condition
/// `kind` and colors that are used as they are. The colors are renumbered like `into_dpa` of the
/// crate does: `c + 1` for min odd and `m - c` for the max kinds, where `m` is the least number
/// at least as large as the largest color that has the right parity (even for max even, odd for
/// max odd). Fails if a result color does not fit into `0..=255`.
fn to_min_even<A: Alphabet, Sem: Clone>(
    aut: &Automaton<DTS<A, Void, Int>, Sem>,
    kind: ParityKind,
) -> PyResult<Automaton<DTS<A, Void, Int>, MinEvenParityCondition>> {
    let ts = aut.ts();
    let (mut low, mut high) = (usize::MAX, 0);
    for q in ts.states() {
        for edge in ts.edges_from(q).into_iter().flatten() {
            low = low.min(usize::from(*edge.color()));
            high = high.max(usize::from(*edge.color()));
        }
    }
    // without edges there is nothing to renumber
    low = low.min(high);
    let c = high + usize::from((high % 2 == 0) != kind.is_even());
    let largest = match kind {
        ParityKind::MinEven => high,
        ParityKind::MinOdd => high + 1,
        ParityKind::MaxEven | ParityKind::MaxOdd => c - low,
    };
    if largest > usize::from(Int::MAX) {
        return Err(PyValueError::new_err(format!(
            "the equivalent min-even automaton needs the color {largest}, but colors are 0..=255"
        )));
    }
    let to_new = |p: Int| {
        (match kind {
            ParityKind::MinEven => usize::from(p),
            ParityKind::MinOdd => usize::from(p) + 1,
            ParityKind::MaxEven | ParityKind::MaxOdd => c - usize::from(p),
        }) as Int
    };
    let (ts, initial, _) = aut.clone().into_parts();
    Ok(ts.map_edge_colors(to_new).with_initial(initial).collect())
}

/// Defines a deterministic parity automaton class for one of the parity conditions other than min
/// even: `$cond` with the kind `$parity_kind`, whose complement is the class `$dual` with the dual
/// condition `$dual_cond`. `to_min_even` gives the equivalent `$min_even` (a `DPA`).
macro_rules! dpa_variant_class {
    (
        $name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $cond:ty, $parity_kind:expr,
        $min_even:ident, $dual:ident, $dual_cond:ty, $doc:expr, { $($more:tt)* }
    ) => {
        omega_class!(
            $name,
            $py_name,
            $kind,
            $pyalpha,
            Int,
            $cond,
            $doc,
            no_emptiness,
            {
                /// Creates the automaton with states `0, ..., num_states - 1`. `edges` are tuples
                /// `(source, symbol, color, target)`; a later edge replaces an earlier one with
                /// the same source and symbol. Raises `ValueError` for states or symbols that do
                /// not exist.
                #[new]
                fn new(
                    alphabet: &$pyalpha,
                    num_states: u32,
                    initial: u32,
                    edges: Vec<(u32, <$kind as Kind>::PySymbol<'_>, Int, u32)>,
                ) -> PyResult<Self> {
                    colored::<$kind, _, _>(alphabet, num_states, initial, edges, Default::default())
                        .map(Self)
                }

                /// The automaton in the HOA format. Raises `HoaError` if it cannot be written.
                fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
                    crate::class::to_hoa(py, &self.0)
                }

                /// A DPA (min even) that accepts the same language. The colors are renumbered
                /// (`c + 1` for min odd, `m - c` for max even and max odd, where `m` is the
                /// least number at least as large as the largest color that is even for max even
                /// and odd for max odd). Raises `ValueError` if a new color does not fit into
                /// `0..=255`.
                fn to_min_even(&self, py: Python<'_>) -> PyResult<$min_even> {
                    py.detach(|| to_min_even(&self.0, $parity_kind)).map($min_even)
                }

                /// The complement: the automaton with the same transitions and colors and the
                /// dual condition (min even and min odd, max even and max odd), which accepts
                /// exactly the words that `self` rejects. The automaton is expected to be
                /// complete.
                fn complement(&self) -> $dual {
                    $dual(self.0.clone().map_acceptance(|_| <$dual_cond>::default()))
                }

                /// Whether the language is empty, decided on `to_min_even()`. The automaton is
                /// expected to be complete. Raises `ValueError` if `to_min_even` does.
                fn is_empty(&self, py: Python<'_>) -> PyResult<bool> {
                    let min_even = py.detach(|| to_min_even(&self.0, $parity_kind))?;
                    Ok(py.detach(|| Emptiness::of(&min_even).holds()))
                }

                /// An accepted word, or `None` if the language is empty. Decided on
                /// `to_min_even()`, raises `ValueError` if that does.
                fn accepting_word(&self, py: Python<'_>) -> PyResult<Option<PyOmegaWord>> {
                    let min_even = py.detach(|| to_min_even(&self.0, $parity_kind))?;
                    Ok(py
                        .detach(|| Emptiness::of(&min_even).witness())
                        .map(|w| <$kind as Kind>::omega_out(&w)))
                }

                $($more)*
            }
        );
    };
}

dpa_variant_class!(
    PyDpaMaxEven,
    "DPAMaxEven",
    Chars,
    PyCharAlphabet,
    MaxEvenParityCondition,
    ParityKind::MaxEven,
    PyDpa,
    PyDpaMaxOdd,
    MaxOddParityCondition,
    "A deterministic parity automaton over a `CharAlphabet` with colors `0..=255` on the edges (others raise `OverflowError`) and the max even condition: a word is accepted if the largest color that its run uses infinitely often is even.\n\n>>> a = CharAlphabet(\"ab\")\n>>> inf_a = DPAMaxEven(a, 1, 0, [(0, \"a\", 2, 0), (0, \"b\", 1, 0)])\n>>> inf_a.accepts(OmegaWord(\"b\", \"ab\"))\nTrue\n>>> inf_a.accepts(OmegaWord(\"a\", \"b\"))\nFalse\n>>> inf_a.to_min_even().accepts(OmegaWord(\"a\", \"b\"))\nFalse\n>>> type(inf_a.complement()).__name__\n'DPAMaxOdd'\n>>> inf_a.complement().accepts(OmegaWord(\"a\", \"b\"))\nTrue\n>>> inf_a.is_empty()\nFalse\n>>> type(parse_hoa(inf_a.to_hoa())).__name__\n'PropDPAMaxEven'",
    {}
);
dpa_variant_class!(
    PyPropDpaMaxEven,
    "PropDPAMaxEven",
    Props,
    PyPropAlphabet,
    MaxEvenParityCondition,
    ParityKind::MaxEven,
    PyPropDpa,
    PyPropDpaMaxOdd,
    MaxOddParityCondition,
    "A deterministic parity automaton over a `PropAlphabet` with the max even condition, see `DPAMaxEven`.",
    {
        /// Reads the first automaton in the HOA text, which has to be a deterministic parity
        /// automaton of exactly the kind `parity max even`; the colors are kept. Raises
        /// `HoaError` otherwise.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::dpa_kind::<MaxEvenParityCondition>(py, text, ParityKind::MaxEven).map(Self)
        }
    }
);
dpa_variant_class!(
    PyDpaMinOdd,
    "DPAMinOdd",
    Chars,
    PyCharAlphabet,
    MinOddParityCondition,
    ParityKind::MinOdd,
    PyDpa,
    PyDpa,
    MinEvenParityCondition,
    "A deterministic parity automaton over a `CharAlphabet` with colors `0..=255` on the edges (others raise `OverflowError`) and the min odd condition: a word is accepted if the least color that its run uses infinitely often is odd. Its complement is a `DPA` (min even).\n\n>>> a = CharAlphabet(\"ab\")\n>>> fin_b = DPAMinOdd(a, 1, 0, [(0, \"a\", 1, 0), (0, \"b\", 0, 0)])\n>>> fin_b.accepts(OmegaWord(\"b\", \"a\"))\nTrue\n>>> fin_b.accepts(OmegaWord(\"a\", \"ab\"))\nFalse\n>>> fin_b.to_min_even().accepts(OmegaWord(\"b\", \"a\"))\nTrue\n>>> type(fin_b.complement()).__name__\n'DPA'\n>>> fin_b.accepting_word() is not None\nTrue\n>>> type(parse_hoa(fin_b.to_hoa())).__name__\n'PropDPAMinOdd'",
    {}
);
dpa_variant_class!(
    PyPropDpaMinOdd,
    "PropDPAMinOdd",
    Props,
    PyPropAlphabet,
    MinOddParityCondition,
    ParityKind::MinOdd,
    PyPropDpa,
    PyPropDpa,
    MinEvenParityCondition,
    "A deterministic parity automaton over a `PropAlphabet` with the min odd condition, see `DPAMinOdd`.",
    {
        /// Reads the first automaton in the HOA text, which has to be a deterministic parity
        /// automaton of exactly the kind `parity min odd`; the colors are kept. Raises
        /// `HoaError` otherwise.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::dpa_kind::<MinOddParityCondition>(py, text, ParityKind::MinOdd).map(Self)
        }
    }
);
dpa_variant_class!(
    PyDpaMaxOdd,
    "DPAMaxOdd",
    Chars,
    PyCharAlphabet,
    MaxOddParityCondition,
    ParityKind::MaxOdd,
    PyDpa,
    PyDpaMaxEven,
    MaxEvenParityCondition,
    "A deterministic parity automaton over a `CharAlphabet` with colors `0..=255` on the edges (others raise `OverflowError`) and the max odd condition: a word is accepted if the largest color that its run uses infinitely often is odd.\n\n>>> a = CharAlphabet(\"ab\")\n>>> inf_a = DPAMaxOdd(a, 1, 0, [(0, \"a\", 1, 0), (0, \"b\", 0, 0)])\n>>> inf_a.accepts(OmegaWord(\"b\", \"ab\"))\nTrue\n>>> inf_a.accepts(OmegaWord(\"a\", \"b\"))\nFalse\n>>> inf_a.to_min_even().accepts(OmegaWord(\"b\", \"ab\"))\nTrue\n>>> type(inf_a.complement()).__name__\n'DPAMaxEven'\n>>> type(parse_hoa(inf_a.to_hoa())).__name__\n'PropDPAMaxOdd'",
    {}
);
dpa_variant_class!(
    PyPropDpaMaxOdd,
    "PropDPAMaxOdd",
    Props,
    PyPropAlphabet,
    MaxOddParityCondition,
    ParityKind::MaxOdd,
    PyPropDpa,
    PyPropDpaMaxEven,
    MaxEvenParityCondition,
    "A deterministic parity automaton over a `PropAlphabet` with the max odd condition, see `DPAMaxOdd`.",
    {
        /// Reads the first automaton in the HOA text, which has to be a deterministic parity
        /// automaton of exactly the kind `parity max odd`; the colors are kept. Raises
        /// `HoaError` otherwise.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::dpa_kind::<MaxOddParityCondition>(py, text, ParityKind::MaxOdd).map(Self)
        }
    }
);

/// Defines a deterministic Rabin or Streett automaton class with the condition `$cond`, whose
/// constructor takes a list of pairs `(fin, inf)` of lists of colors.
macro_rules! pairs_class {
    ($name:ident, $py_name:literal, $kind:ty, $pyalpha:ty, $cond:ident, $doc:expr, { $($more:tt)* }) => {
        omega_class!(
            $name,
            $py_name,
            $kind,
            $pyalpha,
            Int,
            $cond<Int>,
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
                    let condition: $cond<Int> = pairs
                        .into_iter()
                        .map(|(fin, inf)| RabinPair::from_iters(fin, inf))
                        .into();
                    colored::<$kind, _, _>(alphabet, num_states, initial, edges, condition)
                        .map(Self)
                }

                /// The automaton in the HOA format (every color is an acceptance set). Only if
                /// the pairs are `([0], [1])`, `([2], [3])`, ... and the colors are below
                /// `2 * len(pairs)`, the text has the `acc-name` that `from_hoa` and
                /// `parse_hoa` need to read it back. Raises `HoaError` if it cannot be written.
                fn to_hoa(&self, py: Python<'_>) -> PyResult<String> {
                    crate::class::to_hoa(py, &self.0)
                }

                $($more)*
            }
        );
    };
}

pairs_class!(
    PyDra,
    "DRA",
    Chars,
    PyCharAlphabet,
    RabinCondition,
    "A deterministic Rabin automaton over a `CharAlphabet` with colors `0..=255` on the edges (others raise `OverflowError`). A word is accepted if for some pair `(fin, inf)` its run uses no color of `fin` and some color of `inf` infinitely often.\n\n>>> a = CharAlphabet(\"ab\")\n>>> edges = [(0, \"a\", 0, 0), (0, \"b\", 1, 1), (1, \"a\", 0, 0), (1, \"b\", 1, 1)]\n>>> inf_b = DRA(a, 2, 0, edges, [([], [1])])\n>>> inf_b.accepts(OmegaWord(\"\", \"ba\"))\nTrue\n>>> inf_b.accepts(OmegaWord(\"b\", \"a\"))\nFalse\n>>> inf_b.is_empty()\nFalse\n\nThe Streett automaton `DSA` with the same data and every pair `(fin, inf)` replaced by `(inf, fin)` accepts the complement.\n\n>>> DSA(a, 2, 0, edges, [([1], [])]).accepts(OmegaWord(\"b\", \"a\"))\nTrue\n\nThe HOA format can only express the pairs `(fin, inf) = ([0], [1])`, `([2], [3])`, ... (pair `i` is `Fin(2i) & Inf(2i + 1)`) with the colors `0, ..., 2n - 1`, see `to_hoa`.\n\n>>> only_b = DRA(a, 1, 0, [(0, \"a\", 0, 0), (0, \"b\", 1, 0)], [([0], [1])])\n>>> type(parse_hoa(only_b.to_hoa())).__name__\n'PropDRA'",
    {}
);
pairs_class!(
    PyPropDra,
    "PropDRA",
    Props,
    PyPropAlphabet,
    RabinCondition,
    "A deterministic Rabin automaton over a `PropAlphabet`, see `DRA`.",
    {
        /// Reads the first automaton in the HOA text, which has to be deterministic with a
        /// Rabin condition. The edges of a HOA automaton belong to a *set* of acceptance sets,
        /// while an edge of a `PropDRA` has one color: every distinct set of acceptance sets
        /// that occurs on an edge becomes a color (numbered `0, 1, ...` in the order of the
        /// first occurrence, with the states and their edges in the order of `states()` and
        /// `edges_from()`; the empty set is a color too) and the pairs are rewritten
        /// accordingly: a color is in `fin` (`inf`) if its set meets a `fin` (`inf`) set of the
        /// pair. Raises `HoaError` if the text is not such an automaton or if there are more
        /// than 256 different sets.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::dra(py, text).map(Self)
        }
    }
);

pairs_class!(
    PyDsa,
    "DSA",
    Chars,
    PyCharAlphabet,
    StreettCondition,
    "A deterministic Streett automaton over a `CharAlphabet` with colors `0..=255` on the edges (others raise `OverflowError`). A word is accepted if for every pair `(fin, inf)` its run uses no color of `fin` or some color of `inf` infinitely often (the dual of `DRA`; without pairs everything is accepted).\n\n>>> a = CharAlphabet(\"ab\")\n>>> edges = [(0, \"a\", 0, 0), (0, \"b\", 1, 1), (1, \"a\", 0, 0), (1, \"b\", 1, 1)]\n>>> fin_b = DSA(a, 2, 0, edges, [([1], [])])\n>>> fin_b.accepts(OmegaWord(\"b\", \"a\"))\nTrue\n>>> fin_b.accepts(OmegaWord(\"\", \"ba\"))\nFalse\n>>> fin_b.is_empty()\nFalse\n\nThe HOA format can only express the pairs `([0], [1])`, `([2], [3])`, ... (pair `i` is `Fin(2i) | Inf(2i + 1)`) with the colors `0, ..., 2n - 1`, see `to_hoa`.\n\n>>> only_a_finitely = DSA(a, 1, 0, [(0, \"a\", 0, 0), (0, \"b\", 1, 0)], [([0], [1])])\n>>> type(parse_hoa(only_a_finitely.to_hoa())).__name__\n'PropDSA'",
    {}
);
pairs_class!(
    PyPropDsa,
    "PropDSA",
    Props,
    PyPropAlphabet,
    StreettCondition,
    "A deterministic Streett automaton over a `PropAlphabet`, see `DSA`.",
    {
        /// Reads the first automaton in the HOA text, which has to be deterministic with a
        /// Streett condition. The colors are numbered like in `PropDRA.from_hoa`. Raises
        /// `HoaError` if the text is not such an automaton or if there are more than 256
        /// different sets of acceptance sets.
        #[classmethod]
        fn from_hoa(_cls: &Bound<'_, PyType>, py: Python<'_>, text: &str) -> PyResult<Self> {
            crate::hoa::dsa(py, text).map(Self)
        }
    }
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
