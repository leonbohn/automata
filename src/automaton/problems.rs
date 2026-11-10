//! Decision problems on the languages of automata: [`Emptiness`], [`Inclusion`] and
//! [`Equivalence`]. Each problem is stated for one or two automata and answers with a witness (for
//! emptiness) or a counterexample (for inclusion and equivalence) instead of just a boolean.
//!
//! ```
//! use automata::automaton::{Emptiness, Equivalence, Inclusion};
//! use automata::ts::Builder;
//!
//! let dpa = Builder::without_state_colors()
//!     .with_transitions([(0, 'a', 0, 0), (0, 'b', 1, 0)])
//!     .into_dpa(0);
//! let complement = dpa.clone().complement();
//!
//! assert!(Emptiness::of(&dpa).witness().is_some());
//! assert!(Inclusion::of(&dpa).within(&dpa).holds());
//! assert!(Inclusion::of(&dpa).within(&complement).counterexample().is_some());
//! assert!(!Equivalence::of(&dpa).and(&complement).holds());
//! ```
//!
//! Automata over omega words are expected to be complete, as a word on which an automaton has no
//! run is not taken into account.

use super::branching::{CycleCondition, Existential, HistoryDeterministic};
use super::cycles::{self, Colors, Priorities};
use super::{Automaton, DBA, DFA, DPA, NFA};
use crate::DTS;
use crate::alphabet::{Atoms, CharAlphabet, PropAlphabet, PropSymbol, RawSymbolRepr};
use crate::color::Void;
use crate::representation::{FromTransitions, Parts};
use crate::ts::States;
use crate::ts::operations::{Product, ProductIndex};
use crate::ts::{Deterministic, Pointed, StateIndex, SymbolOf, TransitionSystem};
use crate::ts::{EdgeColor, StateColor};
use crate::word::OmegaWord;
use crate::word::ReducedOmegaWord;
use crate::{Int, NTS, math};
use std::hash::Hash;

/// The problem of deciding whether the language of an automaton is empty, see the
/// [module](self) documentation.
#[derive(Debug, Clone, Copy)]
pub struct Emptiness<'a, A>(&'a A);

impl<'a, A> Emptiness<'a, A> {
    /// States the problem for the given automaton.
    pub fn of(automaton: &'a A) -> Self {
        Self(automaton)
    }
}

/// The problem of deciding whether the language of one automaton is included in the language of
/// another. Created with [`Inclusion::of`] and completed with [`Inclusion::within`].
#[derive(Debug, Clone, Copy)]
pub struct Inclusion<'a, A>(&'a A);

impl<'a, A> Inclusion<'a, A> {
    /// Starts the problem for the automaton whose language is supposed to be the smaller one.
    pub fn of(automaton: &'a A) -> Self {
        Self(automaton)
    }

    /// Completes the problem with the automaton whose language is supposed to be the larger one.
    pub fn within<'b, B>(self, superset: &'b B) -> InclusionCheck<'a, 'b, A, B> {
        InclusionCheck {
            subset: self.0,
            superset,
        }
    }
}

/// A fully stated [`Inclusion`] problem, see [`Inclusion::within`].
#[derive(Debug, Clone, Copy)]
pub struct InclusionCheck<'a, 'b, A, B> {
    subset: &'a A,
    superset: &'b B,
}

/// The problem of deciding whether two automata accept the same language. Created with
/// [`Equivalence::of`] and completed with [`Equivalence::and`].
#[derive(Debug, Clone, Copy)]
pub struct Equivalence<'a, A>(&'a A);

impl<'a, A> Equivalence<'a, A> {
    /// Starts the problem for the first automaton.
    pub fn of(automaton: &'a A) -> Self {
        Self(automaton)
    }

    /// Completes the problem with the second automaton.
    pub fn and<'b, B>(self, other: &'b B) -> EquivalenceCheck<'a, 'b, A, B> {
        EquivalenceCheck {
            left: self.0,
            right: other,
        }
    }
}

/// A fully stated [`Equivalence`] problem, see [`Equivalence::and`].
#[derive(Debug, Clone, Copy)]
pub struct EquivalenceCheck<'a, 'b, A, B> {
    left: &'a A,
    right: &'b B,
}

/// The problem of deciding whether the languages of two automata have no word in common. Created
/// with [`Disjointness::of`] and completed with [`Disjointness::and`].
///
/// Unlike [`Emptiness`] of an intersection, this does not build a product automaton first.
#[derive(Debug, Clone, Copy)]
pub struct Disjointness<'a, A>(&'a A);

impl<'a, A> Disjointness<'a, A> {
    /// Starts the problem for the first automaton.
    pub fn of(automaton: &'a A) -> Self {
        Self(automaton)
    }

    /// Completes the problem with the second automaton.
    pub fn and<'b, B>(self, other: &'b B) -> DisjointnessCheck<'a, 'b, A, B> {
        DisjointnessCheck {
            left: self.0,
            right: other,
        }
    }
}

/// A fully stated [`Disjointness`] problem, see [`Disjointness::and`].
#[derive(Debug, Clone, Copy)]
pub struct DisjointnessCheck<'a, 'b, A, B> {
    left: &'a A,
    right: &'b B,
}

// ---- DFA ---------------------------------------------------------------------------------------

impl<D: Deterministic<StateColor = bool>> Emptiness<'_, DFA<D>> {
    /// Returns a length-lexicographically minimal accepted word, or `None` if the language is
    /// empty.
    ///
    /// # Example
    /// ```
    /// use automata::ts::q;
    /// use automata::{automaton::{DFA, Emptiness}, ts::Builder};
    ///
    /// let ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 1), (1, 'a', 1)])
    ///     .into_dts_with_initial(0);
    /// assert_eq!(Emptiness::of(&DFA::from_ts(&ts, [q(1)])).witness(), Some(vec!['a']));
    /// assert_eq!(Emptiness::of(&DFA::from_ts(&ts, [])).witness(), None);
    /// ```
    pub fn witness(&self) -> Option<Vec<SymbolOf<DFA<D>>>> {
        self.0.minimal_representatives_iter().find_map(|rep| {
            let accepting = self.0.state_color(rep.state_index()).is_some_and(|c| *c);
            accepting.then(|| rep.decompose().0)
        })
    }

    /// Returns true if and only if the language is empty.
    pub fn holds(&self) -> bool {
        self.witness().is_none()
    }
}

impl<D, O> InclusionCheck<'_, '_, DFA<D>, DFA<O>>
where
    D: Deterministic<StateColor = bool>,
    O: Deterministic<Alphabet = D::Alphabet, StateColor = bool>,
{
    /// Returns a length-lexicographically minimal word that is accepted by the first but not by
    /// the second automaton, or `None` if the inclusion holds. The product is explored lazily,
    /// so the search stops at the first such word.
    ///
    /// # Example
    /// ```
    /// use automata::ts::q;
    /// use automata::{automaton::{DFA, Inclusion}, ts::Builder};
    ///
    /// let ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 0)])
    ///     .into_dts_with_initial(0);
    /// let ends_in_a = DFA::from_ts(&ts, [q(1)]);
    /// let anything = DFA::from_ts(&ts, [q(0), q(1)]);
    /// assert_eq!(Inclusion::of(&anything).within(&ends_in_a).counterexample(), Some(vec![]));
    /// assert_eq!(Inclusion::of(&ends_in_a).within(&anything).counterexample(), None);
    /// ```
    pub fn counterexample(&self) -> Option<Vec<SymbolOf<DFA<D>>>> {
        product_witness(self.subset, self.superset, |a, b| a && !b)
    }

    /// Returns true if and only if the inclusion holds.
    pub fn holds(&self) -> bool {
        self.counterexample().is_none()
    }
}

impl<D, O> EquivalenceCheck<'_, '_, DFA<D>, DFA<O>>
where
    D: Deterministic<StateColor = bool>,
    O: Deterministic<Alphabet = D::Alphabet, StateColor = bool>,
{
    /// Returns a length-lexicographically minimal word that is accepted by exactly one of the two
    /// automata, or `None` if they are equivalent. A word on which an automaton has no run is
    /// rejected by it.
    pub fn counterexample(&self) -> Option<Vec<SymbolOf<DFA<D>>>> {
        product_witness(self.left, self.right, |a, b| a != b)
    }

    /// Returns true if and only if the two automata accept the same language.
    pub fn holds(&self) -> bool {
        self.counterexample().is_none()
    }
}

impl<D, O> DisjointnessCheck<'_, '_, DFA<D>, DFA<O>>
where
    D: Deterministic<StateColor = bool>,
    O: Deterministic<Alphabet = D::Alphabet, StateColor = bool>,
{
    /// Returns a length-lexicographically minimal word that is accepted by both automata, or
    /// `None` if there is none. The search stops at the first such word.
    pub fn witness(&self) -> Option<Vec<SymbolOf<DFA<D>>>> {
        product_witness(self.left, self.right, |a, b| a && b)
    }

    /// Returns true if and only if no word is accepted by both automata.
    pub fn holds(&self) -> bool {
        self.witness().is_none()
    }
}

/// Finds a length-lexicographically minimal word leading to a reachable pair of states in the
/// product of `left` and `right` whose colors satisfy `pred`. A missing edge leads to a rejecting
/// sink, so words that only one of the automata can read are taken into account.
fn product_witness<D, O>(
    left: &DFA<D>,
    right: &DFA<O>,
    pred: impl Fn(bool, bool) -> bool,
) -> Option<Vec<SymbolOf<DFA<D>>>>
where
    D: Deterministic<StateColor = bool>,
    O: Deterministic<Alphabet = D::Alphabet, StateColor = bool>,
{
    type Pair<L, R> = (Option<L>, Option<R>);
    fn accepts<T: TransitionSystem<StateColor = bool>>(
        ts: &T,
        state: Option<T::StateIndex>,
    ) -> bool {
        state.is_some_and(|q| ts.state_color(q).is_some_and(|c| *c))
    }

    let start: Pair<StateIndex<DFA<D>>, StateIndex<DFA<O>>> =
        (Some(left.initial()), Some(right.initial()));
    let symbols: Vec<_> = left.symbols().collect();
    let mut seen = math::FxIndexSet::default();
    seen.insert(start);
    // every entry is a pair together with the entry it was reached from and the symbol used
    let mut queue: Vec<(_, usize, Option<SymbolOf<DFA<D>>>)> = vec![(start, usize::MAX, None)];
    let mut next = 0;
    while next < queue.len() {
        let (pair, _, _) = queue[next];
        if pred(accepts(left, pair.0), accepts(right, pair.1)) {
            let mut word = Vec::new();
            let mut at = next;
            while let (_, parent, Some(symbol)) = &queue[at] {
                word.push(*symbol);
                at = *parent;
            }
            word.reverse();
            return Some(word);
        }
        if pair != (None, None) {
            for &symbol in &symbols {
                let target = (
                    pair.0.and_then(|q| left.successor(q, symbol)),
                    pair.1.and_then(|q| right.successor(q, symbol)),
                );
                if seen.insert(target) {
                    queue.push((target, next, Some(symbol)));
                }
            }
        }
        next += 1;
    }
    None
}

// ---- omega automata ----------------------------------------------------------------------------

impl<D: Deterministic<EdgeColor = Int>> Emptiness<'_, DPA<D>> {
    /// Returns an ultimately periodic word that is accepted, or `None` if the language is empty.
    /// A single decomposition into strongly connected components is analysed, instead of one for
    /// each priority.
    pub fn witness(&self) -> Option<ReducedOmegaWord<SymbolOf<DPA<D>>>> {
        single_lasso(self.0, |&c| c)
    }

    /// Returns true if and only if the language is empty.
    pub fn holds(&self) -> bool {
        self.witness().is_none()
    }
}

impl<D: Deterministic<EdgeColor = bool>> Emptiness<'_, DBA<D>> {
    /// Returns an ultimately periodic word that is accepted, or `None` if the language is empty.
    pub fn witness(&self) -> Option<ReducedOmegaWord<SymbolOf<DBA<D>>>> {
        single_lasso(self.0, |&c| buchi(c))
    }

    /// Returns true if and only if the language is empty.
    pub fn holds(&self) -> bool {
        self.witness().is_none()
    }
}

impl<D, O> InclusionCheck<'_, '_, DPA<D>, DPA<O>>
where
    D: Deterministic<EdgeColor = Int> + States,
    O: Deterministic<Alphabet = D::Alphabet, EdgeColor = Int> + States,
{
    /// Returns an ultimately periodic word that is accepted by the first but not by the second
    /// automaton, or `None` if the inclusion holds. This uses one product and decomposes it into
    /// strongly connected components, only decomposing those again that cannot be used right
    /// away.
    pub fn counterexample(&self) -> Option<ReducedOmegaWord<SymbolOf<DPA<D>>>> {
        product_lasso(self.subset, self.superset, |&c| c, &[(true, false)])
    }

    /// Returns true if and only if the inclusion holds.
    pub fn holds(&self) -> bool {
        self.counterexample().is_none()
    }
}

impl<D, O> EquivalenceCheck<'_, '_, DPA<D>, DPA<O>>
where
    D: Deterministic<EdgeColor = Int> + States,
    O: Deterministic<Alphabet = D::Alphabet, EdgeColor = Int> + States,
{
    /// Returns an ultimately periodic word that is accepted by exactly one of the two automata,
    /// or `None` if they are equivalent.
    pub fn counterexample(&self) -> Option<ReducedOmegaWord<SymbolOf<DPA<D>>>> {
        product_lasso(
            self.left,
            self.right,
            |&c| c,
            &[(true, false), (false, true)],
        )
    }

    /// Returns true if and only if the two automata accept the same language.
    pub fn holds(&self) -> bool {
        self.counterexample().is_none()
    }
}

impl<D, O> InclusionCheck<'_, '_, DBA<D>, DBA<O>>
where
    D: Deterministic<EdgeColor = bool> + States,
    O: Deterministic<Alphabet = D::Alphabet, EdgeColor = bool> + States,
{
    /// Returns an ultimately periodic word that is accepted by the first but not by the second
    /// automaton, or `None` if the inclusion holds.
    pub fn counterexample(&self) -> Option<ReducedOmegaWord<SymbolOf<DBA<D>>>> {
        product_lasso(self.subset, self.superset, |&c| buchi(c), &[(true, false)])
    }

    /// Returns true if and only if the inclusion holds.
    pub fn holds(&self) -> bool {
        self.counterexample().is_none()
    }
}

impl<D, O> EquivalenceCheck<'_, '_, DBA<D>, DBA<O>>
where
    D: Deterministic<EdgeColor = bool> + States,
    O: Deterministic<Alphabet = D::Alphabet, EdgeColor = bool> + States,
{
    /// Returns an ultimately periodic word that is accepted by exactly one of the two automata,
    /// or `None` if they are equivalent.
    pub fn counterexample(&self) -> Option<ReducedOmegaWord<SymbolOf<DBA<D>>>> {
        product_lasso(
            self.left,
            self.right,
            |&c| buchi(c),
            &[(true, false), (false, true)],
        )
    }

    /// Returns true if and only if the two automata accept the same language.
    pub fn holds(&self) -> bool {
        self.counterexample().is_none()
    }
}

// ---- nondeterministic automata ------------------------------------------------------------------

impl<T: TransitionSystem<StateColor = bool>> Emptiness<'_, NFA<T>> {
    /// Returns a length-lexicographically minimal accepted word, or `None` if the language is
    /// empty.
    pub fn witness(&self) -> Option<Vec<SymbolOf<T>>> {
        self.0.minimal_representatives_iter().find_map(|rep| {
            let accepting = self.0.state_color(rep.state_index()).is_some_and(|c| *c);
            accepting.then(|| rep.decompose().0)
        })
    }

    /// Returns true if and only if the language is empty.
    pub fn holds(&self) -> bool {
        self.witness().is_none()
    }
}

impl<T, O> InclusionCheck<'_, '_, NFA<T>, NFA<O>>
where
    T: States<StateColor = bool>,
    O: States<Alphabet = T::Alphabet, StateColor = bool>,
{
    /// Returns a length-lexicographically minimal word that is accepted by the first but not by
    /// the second automaton, or `None` if the inclusion holds. Both are determinized first, see
    /// [`NFA::determinize`].
    pub fn counterexample(&self) -> Option<Vec<SymbolOf<T>>> {
        let (subset, superset) = (self.subset.determinize(), self.superset.determinize());
        Inclusion::of(&subset).within(&superset).counterexample()
    }

    /// Returns true if and only if the inclusion holds.
    pub fn holds(&self) -> bool {
        self.counterexample().is_none()
    }
}

impl<T, O> EquivalenceCheck<'_, '_, NFA<T>, NFA<O>>
where
    T: States<StateColor = bool>,
    O: States<Alphabet = T::Alphabet, StateColor = bool>,
{
    /// Returns a length-lexicographically minimal word that is accepted by exactly one of the two
    /// automata, or `None` if they are equivalent. Both are determinized first.
    pub fn counterexample(&self) -> Option<Vec<SymbolOf<T>>> {
        let (left, right) = (self.left.determinize(), self.right.determinize());
        Equivalence::of(&left).and(&right).counterexample()
    }

    /// Returns true if and only if the two automata accept the same language.
    pub fn holds(&self) -> bool {
        self.counterexample().is_none()
    }
}

impl<T, C> Emptiness<'_, Automaton<T, Existential<C>>>
where
    T: TransitionSystem,
    C: CycleCondition<Color = EdgeColor<T>>,
    EdgeColor<T>: Hash + Eq,
{
    /// Returns an ultimately periodic word that is accepted, or `None` if the language is empty.
    /// This works for every nondeterministic omega automaton ([`super::NBA`], [`super::NCA`],
    /// [`super::NPA`], [`super::NRA`], [`super::NMA`], ...), see [`CycleCondition`].
    ///
    /// ```
    /// use automata::prelude::*;
    ///
    /// let nba = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', false, 0), (0, 'b', false, 1), (1, 'b', true, 1)])
    ///     .into_nba(0);
    /// let word = Emptiness::of(&nba).witness().unwrap();
    /// assert!(nba.accepts(&word));
    /// ```
    pub fn witness(&self) -> Option<ReducedOmegaWord<SymbolOf<T>>> {
        cycles::lasso(
            self.0.ts(),
            self.0.initial(),
            &Colors(&self.0.acceptance().0),
        )
    }

    /// Returns true if and only if the language is empty.
    pub fn holds(&self) -> bool {
        self.witness().is_none()
    }
}

/// Emptiness of deterministic omega automata without a dedicated parity search, by the same search
/// as for nondeterministic ones (a deterministic automaton accepts some word if and only if a
/// reachable cycle is accepting).
macro_rules! emptiness_via_cycles {
    ($($alias:ident => $cond:ty),*) => {$(
        impl<D> Emptiness<'_, super::$alias<D>>
        where
            D: TransitionSystem,
            $cond: CycleCondition<Color = EdgeColor<D>>,
            EdgeColor<D>: Hash + Ord,
        {
            /// Returns an ultimately periodic word that is accepted, or `None` if the language is
            /// empty.
            pub fn witness(&self) -> Option<ReducedOmegaWord<SymbolOf<D>>> {
                cycles::lasso(self.0.ts(), self.0.initial(), &Colors(self.0.acceptance()))
            }

            /// Returns true if and only if the language is empty.
            pub fn holds(&self) -> bool {
                self.witness().is_none()
            }
        }
    )*};
}
emptiness_via_cycles!(
    DCA => super::CoBuchiCondition,
    DRA => super::RabinCondition<EdgeColor<D>>,
    DSA => super::StreettCondition<EdgeColor<D>>,
    DMA => super::MullerCondition<EdgeColor<D>>
);

impl<T, C> Emptiness<'_, Automaton<T, HistoryDeterministic<C>>>
where
    T: TransitionSystem,
    C: CycleCondition<Color = EdgeColor<T>>,
    EdgeColor<T>: Hash + Eq,
{
    /// Returns an ultimately periodic word that is accepted, or `None` if the language is empty,
    /// like for [`Existential`] automata.
    pub fn witness(&self) -> Option<ReducedOmegaWord<SymbolOf<T>>> {
        cycles::lasso(
            self.0.ts(),
            self.0.initial(),
            &Colors(&self.0.acceptance().0),
        )
    }

    /// Returns true if and only if the language is empty.
    pub fn holds(&self) -> bool {
        self.witness().is_none()
    }
}

/// A Büchi automaton is a parity automaton with priority 0 on accepting and 1 on other edges.
fn buchi(accepting: bool) -> Int {
    if accepting { 0 } else { 1 }
}

/// The least priority of the given parity that occurs on an edge of `ts`. No cycle can have a
/// least priority of that parity that is smaller, so edges below it can be ignored right away.
fn least_priority<T: States>(
    ts: &T,
    priority: impl Fn(&T::EdgeColor) -> Int,
    even: bool,
) -> Option<Int> {
    ts.states()
        .filter_map(|q| ts.edges_from(q))
        .flatten()
        .map(|edge| priority(edge.color()))
        .filter(|p| p.is_multiple_of(2) == even)
        .min()
}

/// An accepted word of a deterministic parity or Büchi automaton, see [`cycles::lasso`].
fn single_lasso<L, S>(
    automaton: &Automaton<L, S>,
    priority: impl Fn(&L::EdgeColor) -> Int,
) -> Option<ReducedOmegaWord<SymbolOf<L>>>
where
    L: Deterministic,
{
    let priorities = Priorities {
        priorities: |c: &L::EdgeColor| (priority(c), 0),
        accepted: (true, true),
    };
    cycles::lasso(automaton, automaton.initial(), &priorities)
}

/// Looks for a word whose run in the product of `left` and `right` has one of the given
/// acceptances (as seen by the min-even parity condition on `priority`) in both automata. The
/// product is built once, with its edge labels computed once, and shared by all acceptances.
fn product_lasso<L, R, S>(
    left: &Automaton<L, S>,
    right: &Automaton<R, S>,
    priority: impl Fn(&L::EdgeColor) -> Int + Copy,
    accepted: &[(bool, bool)],
) -> Option<ReducedOmegaWord<SymbolOf<L>>>
where
    L: Deterministic + States,
    R: Deterministic<Alphabet = L::Alphabet, EdgeColor = L::EdgeColor> + States,
{
    // Without an edge of the right parity, no cycle can have the wanted least priority. The edges
    // below these priorities must not be removed, as they may be needed to reach a good cycle.
    let possible: Vec<_> = accepted
        .iter()
        .copied()
        .filter(|&(l, r)| {
            least_priority(left, priority, l).is_some()
                && least_priority(right, priority, r).is_some()
        })
        .collect();
    if possible.is_empty() {
        return None;
    }
    // The search decomposes the product repeatedly; a lazy product would recompute its edge
    // labels (BDD intersections for propositional alphabets) every time.
    let product = explore_product(left, right);
    let initial = crate::ts::q(0);
    possible.into_iter().find_map(|accepted| {
        let priorities = Priorities {
            priorities: |(l, r): &(L::EdgeColor, L::EdgeColor)| (priority(l), priority(r)),
            accepted,
        };
        cycles::lasso(&product, initial, &priorities)
    })
}

/// The part of the product of `left` and `right` that is reachable from the pair of initial
/// states, stored with its edges (so that each edge label is computed once). The initial state
/// has index 0.
fn explore_product<L, R, S>(
    left: &Automaton<L, S>,
    right: &Automaton<R, S>,
) -> NTS<L::Alphabet, Void, (L::EdgeColor, L::EdgeColor)>
where
    L: Deterministic + States,
    R: Deterministic<Alphabet = L::Alphabet, EdgeColor = L::EdgeColor> + States,
{
    let product = left.ts_product(right);
    let mut states = math::FxIndexSet::default();
    states.insert(ProductIndex(left.initial(), right.initial()));
    let mut edges = Vec::new();
    let mut next = 0;
    while let Some(&source) = states.get_index(next) {
        next += 1;
        for edge in product.edges_from(source).into_iter().flatten() {
            let (source, expression, color, target) = edge.into_tuple();
            states.insert(target);
            edges.push((source, expression, color, target));
        }
    }
    NTS::from_transitions(Parts {
        alphabet: left.alphabet().clone(),
        states: states.into_iter().map(|q| (q, Void)),
        edges: edges.into_iter(),
        initial: (),
    })
}

// ---- propositional alphabets over atoms ---------------------------------------------------------
//
// The methods `*_by_atoms` solve a problem on automata over a `PropAlphabet` by relabeling them
// to the indexed alphabet of the atoms of all their edge labels (see `Atoms`), which makes
// the intersection of labels an equality test. Words are translated back to propositional
// symbols. The automata must be over the same atomic propositions.

/// Relabels `automaton` to the letters of `atoms`, see [`Atoms::split_edges`]. The labels of
/// `automaton` must be unions of atoms.
fn split_automaton<R, T, S>(
    atoms: &Atoms<R>,
    automaton: &Automaton<T, S>,
) -> Automaton<DTS<CharAlphabet, StateColor<T>, EdgeColor<T>>, S>
where
    R: RawSymbolRepr,
    T: States<Alphabet = PropAlphabet<R>>,
    S: Clone,
{
    let ts: DTS<CharAlphabet, StateColor<T>, EdgeColor<T>> = atoms.split_edges(automaton.ts());
    // states are numbered in the order of `states()`, which may skip removed ones
    let initial = automaton
        .ts()
        .states()
        .position(|q| q == automaton.initial())
        .expect("the initial state is a state");
    Automaton::from_parts_with_acceptance(
        ts,
        crate::ts::q(initial as u32),
        automaton.acceptance().clone(),
    )
}

/// Translates a word over the letters of `atoms` to propositional symbols.
fn lift_word<R: RawSymbolRepr>(atoms: &Atoms<R>, word: Vec<char>) -> Vec<PropSymbol<R>> {
    word.into_iter()
        .map(|c| atoms.symbol_of(c).expect("the letter belongs to an atom"))
        .collect()
}

/// Translates an ultimately periodic word over the letters of `atoms` to propositional symbols.
fn lift_lasso<R: RawSymbolRepr>(
    atoms: &Atoms<R>,
    word: ReducedOmegaWord<char>,
) -> ReducedOmegaWord<PropSymbol<R>> {
    ReducedOmegaWord::from_raw_parts(
        lift_word(atoms, word.raw_word().to_vec()),
        word.loop_index(),
    )
}

/// The atoms of the edge labels of both automata.
fn joint_atoms<R, T, O, S>(left: &Automaton<T, S>, right: &Automaton<O, S>) -> Atoms<R>
where
    R: RawSymbolRepr,
    T: States<Alphabet = PropAlphabet<R>>,
    O: States<Alphabet = PropAlphabet<R>>,
{
    Atoms::new(
        left.alphabet().aps(),
        Atoms::labels(left.ts()).chain(Atoms::labels(right.ts())),
    )
}

impl<R, D> Emptiness<'_, DFA<D>>
where
    R: RawSymbolRepr,
    D: Deterministic<Alphabet = PropAlphabet<R>, StateColor = bool> + States,
{
    /// Like [`Self::witness`], but works over the atoms of the edge labels instead of over
    /// expressions. The word is not necessarily length-lexicographically minimal.
    pub fn witness_by_atoms(&self) -> Option<Vec<PropSymbol<R>>> {
        let atoms = Atoms::of(self.0.alphabet(), [self.0.ts()]);
        let split = split_automaton(&atoms, self.0);
        Emptiness::of(&split)
            .witness()
            .map(|w| lift_word(&atoms, w))
    }

    /// Returns true if and only if the language is empty, see [`Self::witness_by_atoms`].
    pub fn holds_by_atoms(&self) -> bool {
        self.witness_by_atoms().is_none()
    }
}

impl<R, D> Emptiness<'_, DPA<D>>
where
    R: RawSymbolRepr,
    D: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = Int> + States,
{
    /// Like [`Self::witness`], but works over the atoms of the edge labels instead of over
    /// expressions.
    pub fn witness_by_atoms(&self) -> Option<ReducedOmegaWord<PropSymbol<R>>> {
        let atoms = Atoms::of(self.0.alphabet(), [self.0.ts()]);
        let split = split_automaton(&atoms, self.0);
        Emptiness::of(&split)
            .witness()
            .map(|w| lift_lasso(&atoms, w))
    }

    /// Returns true if and only if the language is empty, see [`Self::witness_by_atoms`].
    pub fn holds_by_atoms(&self) -> bool {
        self.witness_by_atoms().is_none()
    }
}

impl<R, D> Emptiness<'_, DBA<D>>
where
    R: RawSymbolRepr,
    D: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = bool> + States,
{
    /// Like [`Self::witness`], but works over the atoms of the edge labels instead of over
    /// expressions.
    pub fn witness_by_atoms(&self) -> Option<ReducedOmegaWord<PropSymbol<R>>> {
        let atoms = Atoms::of(self.0.alphabet(), [self.0.ts()]);
        let split = split_automaton(&atoms, self.0);
        Emptiness::of(&split)
            .witness()
            .map(|w| lift_lasso(&atoms, w))
    }

    /// Returns true if and only if the language is empty, see [`Self::witness_by_atoms`].
    pub fn holds_by_atoms(&self) -> bool {
        self.witness_by_atoms().is_none()
    }
}

impl<R, D, O> InclusionCheck<'_, '_, DFA<D>, DFA<O>>
where
    R: RawSymbolRepr,
    D: Deterministic<Alphabet = PropAlphabet<R>, StateColor = bool> + States,
    O: Deterministic<Alphabet = PropAlphabet<R>, StateColor = bool> + States,
{
    /// Like [`Self::counterexample`], but works over the atoms of the edge labels of both
    /// automata instead of over expressions. Both must be over the same atomic propositions.
    pub fn counterexample_by_atoms(&self) -> Option<Vec<PropSymbol<R>>> {
        let atoms = joint_atoms(self.subset, self.superset);
        let (subset, superset) = (
            split_automaton(&atoms, self.subset),
            split_automaton(&atoms, self.superset),
        );
        Inclusion::of(&subset)
            .within(&superset)
            .counterexample()
            .map(|w| lift_word(&atoms, w))
    }

    /// Returns true if and only if the inclusion holds, see [`Self::counterexample_by_atoms`].
    pub fn holds_by_atoms(&self) -> bool {
        self.counterexample_by_atoms().is_none()
    }
}

impl<R, D, O> InclusionCheck<'_, '_, DPA<D>, DPA<O>>
where
    R: RawSymbolRepr,
    D: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = Int> + States,
    O: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = Int> + States,
{
    /// Like [`Self::counterexample`], but works over the atoms of the edge labels of both
    /// automata instead of over expressions. Both must be over the same atomic propositions.
    pub fn counterexample_by_atoms(&self) -> Option<ReducedOmegaWord<PropSymbol<R>>> {
        let atoms = joint_atoms(self.subset, self.superset);
        let (subset, superset) = (
            split_automaton(&atoms, self.subset),
            split_automaton(&atoms, self.superset),
        );
        Inclusion::of(&subset)
            .within(&superset)
            .counterexample()
            .map(|w| lift_lasso(&atoms, w))
    }

    /// Returns true if and only if the inclusion holds, see [`Self::counterexample_by_atoms`].
    pub fn holds_by_atoms(&self) -> bool {
        self.counterexample_by_atoms().is_none()
    }
}

impl<R, D, O> InclusionCheck<'_, '_, DBA<D>, DBA<O>>
where
    R: RawSymbolRepr,
    D: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = bool> + States,
    O: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = bool> + States,
{
    /// Like [`Self::counterexample`], but works over the atoms of the edge labels of both
    /// automata instead of over expressions. Both must be over the same atomic propositions.
    pub fn counterexample_by_atoms(&self) -> Option<ReducedOmegaWord<PropSymbol<R>>> {
        let atoms = joint_atoms(self.subset, self.superset);
        let (subset, superset) = (
            split_automaton(&atoms, self.subset),
            split_automaton(&atoms, self.superset),
        );
        Inclusion::of(&subset)
            .within(&superset)
            .counterexample()
            .map(|w| lift_lasso(&atoms, w))
    }

    /// Returns true if and only if the inclusion holds, see [`Self::counterexample_by_atoms`].
    pub fn holds_by_atoms(&self) -> bool {
        self.counterexample_by_atoms().is_none()
    }
}

impl<R, D, O> EquivalenceCheck<'_, '_, DFA<D>, DFA<O>>
where
    R: RawSymbolRepr,
    D: Deterministic<Alphabet = PropAlphabet<R>, StateColor = bool> + States,
    O: Deterministic<Alphabet = PropAlphabet<R>, StateColor = bool> + States,
{
    /// Like [`Self::counterexample`], but works over the atoms of the edge labels of both
    /// automata instead of over expressions. Both must be over the same atomic propositions.
    pub fn counterexample_by_atoms(&self) -> Option<Vec<PropSymbol<R>>> {
        let atoms = joint_atoms(self.left, self.right);
        let (left, right) = (
            split_automaton(&atoms, self.left),
            split_automaton(&atoms, self.right),
        );
        Equivalence::of(&left)
            .and(&right)
            .counterexample()
            .map(|w| lift_word(&atoms, w))
    }

    /// Returns true if and only if the automata are equivalent, see
    /// [`Self::counterexample_by_atoms`].
    pub fn holds_by_atoms(&self) -> bool {
        self.counterexample_by_atoms().is_none()
    }
}

impl<R, D, O> EquivalenceCheck<'_, '_, DPA<D>, DPA<O>>
where
    R: RawSymbolRepr,
    D: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = Int> + States,
    O: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = Int> + States,
{
    /// Like [`Self::counterexample`], but works over the atoms of the edge labels of both
    /// automata instead of over expressions. Both must be over the same atomic propositions.
    pub fn counterexample_by_atoms(&self) -> Option<ReducedOmegaWord<PropSymbol<R>>> {
        let atoms = joint_atoms(self.left, self.right);
        let (left, right) = (
            split_automaton(&atoms, self.left),
            split_automaton(&atoms, self.right),
        );
        Equivalence::of(&left)
            .and(&right)
            .counterexample()
            .map(|w| lift_lasso(&atoms, w))
    }

    /// Returns true if and only if the automata are equivalent, see
    /// [`Self::counterexample_by_atoms`].
    pub fn holds_by_atoms(&self) -> bool {
        self.counterexample_by_atoms().is_none()
    }
}

impl<R, D, O> EquivalenceCheck<'_, '_, DBA<D>, DBA<O>>
where
    R: RawSymbolRepr,
    D: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = bool> + States,
    O: Deterministic<Alphabet = PropAlphabet<R>, EdgeColor = bool> + States,
{
    /// Like [`Self::counterexample`], but works over the atoms of the edge labels of both
    /// automata instead of over expressions. Both must be over the same atomic propositions.
    pub fn counterexample_by_atoms(&self) -> Option<ReducedOmegaWord<PropSymbol<R>>> {
        let atoms = joint_atoms(self.left, self.right);
        let (left, right) = (
            split_automaton(&atoms, self.left),
            split_automaton(&atoms, self.right),
        );
        Equivalence::of(&left)
            .and(&right)
            .counterexample()
            .map(|w| lift_lasso(&atoms, w))
    }

    /// Returns true if and only if the automata are equivalent, see
    /// [`Self::counterexample_by_atoms`].
    pub fn holds_by_atoms(&self) -> bool {
        self.counterexample_by_atoms().is_none()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::Builder;
    use crate::ts::q;

    #[test]
    fn dfa_problems() {
        let ts = Builder::without_colors()
            .with_edges([(0, 'a', 0), (0, 'b', 1), (1, 'a', 0), (1, 'b', 1)])
            .into_dts_with_initial(0);
        let all = DFA::from_ts(&ts, [q(0), q(1)]);
        let some = DFA::from_ts(&ts, [q(0)]);
        assert!(Equivalence::of(&all).and(&all).holds());
        assert!(!Equivalence::of(&all).and(&some).holds());
        assert_eq!(
            Equivalence::of(&some).and(&all).counterexample(),
            Some(vec!['b'])
        );
        assert!(Inclusion::of(&some).within(&all).holds());
        assert_eq!(
            Inclusion::of(&all).within(&some).counterexample(),
            Some(vec!['b'])
        );
        assert!(Emptiness::of(&DFA::from_ts(&ts, [])).holds());
        assert!(!Emptiness::of(&some).holds());
    }

    #[test]
    fn dfa_equivalence_of_incomplete_dfas_counts_missing_runs_as_rejecting() {
        let edges = [(0, 'a', 0), (1, 'a', 2)];
        let from = |initial| {
            Builder::without_colors()
                .with_edges(edges)
                .into_dts_with_initial(initial)
        };
        let looping = from(0);
        let once = from(1);
        let looping = DFA::from_ts(&looping, [q(0)]);
        let once = DFA::from_ts(&once, [q(1), q(2)]);
        assert_eq!(
            Equivalence::of(&looping).and(&once).counterexample(),
            Some(vec!['a', 'a'])
        );
        assert!(Equivalence::of(&once).and(&once).holds());
    }

    fn dpa(edges: impl IntoIterator<Item = (u32, char, Int, u32)>) -> DPA {
        Builder::without_state_colors()
            .with_transitions(edges)
            .into_dpa(0)
    }

    #[test]
    fn dpa_inclusion_needs_edges_below_the_cycle_priorities() {
        // the good cycle is only reachable over an edge whose priority is below the ones on it
        let rejecting = dpa([(0, 'a', 0, 1), (1, 'a', 1, 1)]);
        let accepting = dpa([(0, 'a', 1, 1), (1, 'a', 2, 1)]);
        assert!(!Inclusion::of(&accepting).within(&rejecting).holds());
        assert!(!Equivalence::of(&accepting).and(&rejecting).holds());
    }

    #[test]
    fn dpa_problems() {
        // infinitely many a's
        let inf_a = dpa([(0, 'a', 0, 0), (0, 'b', 1, 0)]);
        // infinitely many b's
        let inf_b = dpa([(0, 'a', 1, 0), (0, 'b', 0, 0)]);
        // everything and nothing
        let all = dpa([(0, 'a', 0, 0), (0, 'b', 2, 0)]);
        let none = dpa([(0, 'a', 1, 0), (0, 'b', 3, 0)]);

        assert!(Emptiness::of(&none).holds());
        assert!(!Emptiness::of(&inf_a).holds());
        let word = Emptiness::of(&inf_b).witness().unwrap();
        assert!(inf_b.accepts(&word));

        assert!(Inclusion::of(&inf_a).within(&all).holds());
        assert!(Inclusion::of(&none).within(&inf_a).holds());
        let cex = Inclusion::of(&all).within(&inf_a).counterexample().unwrap();
        assert!(all.accepts(&cex) && !inf_a.accepts(&cex));
        let cex = Inclusion::of(&inf_a)
            .within(&inf_b)
            .counterexample()
            .unwrap();
        assert!(inf_a.accepts(&cex) && !inf_b.accepts(&cex));

        assert!(Equivalence::of(&inf_a).and(&inf_a).holds());
        assert!(
            Equivalence::of(&inf_a)
                .and(&inf_a.clone().complement().complement())
                .holds()
        );
        let cex = Equivalence::of(&none).and(&inf_b).counterexample().unwrap();
        assert!(inf_b.accepts(&cex) && !none.accepts(&cex));
    }

    #[test]
    fn dpa_inclusion_needs_decomposing_components() {
        // The product is one component whose least priorities are odd for the first automaton, but
        // the words in `a^* b^ω` can avoid the edges that spoil it.
        let first = dpa([
            (0, 'a', 1, 0),
            (0, 'b', 2, 1),
            (1, 'a', 2, 1),
            (1, 'b', 2, 0),
        ]);
        let second = dpa([(0, 'a', 1, 0), (0, 'b', 1, 0)]);
        let cex = Inclusion::of(&first)
            .within(&second)
            .counterexample()
            .unwrap();
        assert!(first.accepts(&cex) && !second.accepts(&cex));
    }

    #[test]
    fn prefix_partition_agrees_with_pairwise_equivalence() {
        // some of the states are language-equivalent, others are not
        let dpa = dpa([
            (0, 'a', 0, 1),
            (0, 'b', 1, 3),
            (1, 'a', 0, 2),
            (1, 'b', 2, 3),
            (2, 'a', 0, 1),
            (2, 'b', 1, 3),
            (3, 'a', 1, 3),
            (3, 'b', 1, 3),
        ]);
        let partition = dpa.prefix_partition();
        let states: Vec<_> = dpa.reachable_state_indices().collect();
        for &p in &states {
            for &q in &states {
                let (from_p, from_q) = (DPA::from_parts(&dpa, p), DPA::from_parts(&dpa, q));
                let same_class = partition.iter().any(|c| c.contains(&p) && c.contains(&q));
                assert_eq!(same_class, Equivalence::of(&from_p).and(&from_q).holds());
            }
        }
        assert!(partition.len() < states.len());
    }

    #[test]
    fn dba_problems() {
        let ts = |edges: [(u32, char, bool, u32); 2]| {
            Builder::without_state_colors()
                .with_transitions(edges)
                .into_dts_with_initial(0)
        };
        let inf_a: DBA<_> = ts([(0, 'a', true, 0), (0, 'b', false, 0)]).into();
        let inf_b: DBA<_> = ts([(0, 'a', false, 0), (0, 'b', true, 0)]).into();
        let none: DBA<_> = ts([(0, 'a', false, 0), (0, 'b', false, 0)]).into();
        assert!(Emptiness::of(&none).holds());
        assert!(!Emptiness::of(&inf_a).holds());
        assert!(Inclusion::of(&none).within(&inf_a).holds());
        let cex = Inclusion::of(&inf_a)
            .within(&inf_b)
            .counterexample()
            .unwrap();
        assert!(inf_a.accepts(&cex) && !inf_b.accepts(&cex));
        assert!(Equivalence::of(&inf_a).and(&inf_a).holds());
        assert!(!Equivalence::of(&inf_a).and(&inf_b).holds());
    }

    /// A parity automaton over `aps` atomic propositions with the given body, in which a priority
    /// of 0 is accepting.
    #[cfg(feature = "hoa")]
    fn prop_dpa(
        aps: usize,
        body: &str,
    ) -> DPA<crate::DTS<crate::alphabet::PropAlphabet, crate::Void, Int>> {
        use crate::hoa::HoaString;
        let names = (0..aps)
            .map(|i| format!("\"p{i}\""))
            .collect::<Vec<_>>()
            .join(" ");
        let text = format!(
            "HOA: v1\nStates: 2\nStart: 0\nacc-name: parity min even 2\nAcceptance: 2 Inf(0) | Fin(1)\nAP: {aps} {names}\n--BODY--\n{body}\n--END--\n"
        );
        HoaString::from(text)
            .pop::<crate::ts::Det<crate::ts::Linked>>()
            .and_then(|a| a.into_dpa().ok())
            .expect("a valid parity automaton")
    }

    #[cfg(feature = "hoa")]
    #[test]
    fn emptiness_by_atoms_agrees_with_expressions() {
        let a = prop_dpa(1, "State: 0\n[t] 1 {0}\nState: 1\n[0] 0 {1}\n[!0] 1 {1}");
        let never = prop_dpa(1, "State: 0\n[t] 1 {1}\nState: 1\n[t] 0 {1}");
        assert!(Emptiness::of(&never).holds_by_atoms());
        let word = Emptiness::of(&a).witness_by_atoms().unwrap();
        assert!(a.accepts(&word));
        assert!(!Emptiness::of(&a).holds_by_atoms());
    }

    #[cfg(feature = "hoa")]
    #[test]
    fn inclusion_by_atoms_agrees_with_expressions() {
        let a = prop_dpa(1, "State: 0\n[t] 1 {0}\nState: 1\n[0] 0 {1}\n[!0] 1 {1}");
        let never = prop_dpa(1, "State: 0\n[t] 1 {1}\nState: 1\n[t] 0 {1}");
        let a_split = prop_dpa(
            1,
            "State: 0\n[0] 1 {0}\n[!0] 1 {0}\nState: 1\n[0] 0 {1}\n[!0] 1 {1}",
        );
        assert!(Inclusion::of(&a_split).within(&a).holds_by_atoms());
        assert!(Inclusion::of(&never).within(&a).holds_by_atoms());
        let cex = Inclusion::of(&a).within(&never).counterexample_by_atoms();
        assert!(cex.is_some_and(|w| a.accepts(&w) && !never.accepts(&w)));
    }

    #[cfg(feature = "hoa")]
    #[test]
    fn equivalence_by_atoms_agrees_with_expressions() {
        let a = prop_dpa(1, "State: 0\n[t] 1 {0}\nState: 1\n[0] 0 {1}\n[!0] 1 {1}");
        let never = prop_dpa(1, "State: 0\n[t] 1 {1}\nState: 1\n[t] 0 {1}");
        let a_split = prop_dpa(
            1,
            "State: 0\n[0] 1 {0}\n[!0] 1 {0}\nState: 1\n[0] 0 {1}\n[!0] 1 {1}",
        );
        assert!(Equivalence::of(&a).and(&a_split).holds_by_atoms());
        let cex = Equivalence::of(&a).and(&never).counterexample_by_atoms();
        assert!(cex.is_some_and(|w| a.accepts(&w) != never.accepts(&w)));
    }

    #[cfg(feature = "hoa")]
    #[test]
    fn omega_problems_with_edges_labeled_by_formulas_that_are_no_valuations() {
        // the `t`-labeled edges overlap with the edges of the others without being equal to them
        let a = prop_dpa(1, "State: 0\n[t] 1 {0}\nState: 1\n[0] 0 {1}\n[!0] 1 {1}");
        let never = prop_dpa(1, "State: 0\n[t] 1 {1}\nState: 1\n[t] 0 {1}");
        assert!(Emptiness::of(&never).holds());
        assert!(!Emptiness::of(&a).holds());
        let a_split = prop_dpa(
            1,
            "State: 0\n[0] 1 {0}\n[!0] 1 {0}\nState: 1\n[0] 0 {1}\n[!0] 1 {1}",
        );
        assert!(Equivalence::of(&a).and(&a_split).holds());
        assert!(Inclusion::of(&a_split).within(&a).holds());
        let cex = Inclusion::of(&a).within(&never).counterexample();
        assert!(cex.is_some_and(|w| a.accepts(&w) && !never.accepts(&w)));
        assert!(!Inclusion::of(&a).within(&never).holds());
        assert!(!Equivalence::of(&a).and(&never).holds());
        assert!(Inclusion::of(&never).within(&a).holds());
    }

    #[cfg(feature = "hoa")]
    #[test]
    fn omega_problems_with_partially_overlapping_formulas() {
        // over two propositions, `p0` and `p1` overlap without one containing the other
        let left = prop_dpa(2, "State: 0\n[0] 0 {0}\n[!0] 1 {1}\nState: 1\n[t] 1 {1}");
        let right = prop_dpa(2, "State: 0\n[1] 0 {0}\n[!1] 1 {1}\nState: 1\n[t] 1 {1}");
        let cex = Inclusion::of(&left)
            .within(&right)
            .counterexample()
            .unwrap();
        assert!(left.accepts(&cex) && !right.accepts(&cex));
        let cex = Equivalence::of(&left).and(&right).counterexample().unwrap();
        assert_ne!(left.accepts(&cex), right.accepts(&cex));
        assert!(Equivalence::of(&left).and(&left).holds());
    }

    #[cfg(feature = "hoa")]
    #[test]
    fn prefix_partition_with_edges_labeled_by_formulas_that_are_no_valuations() {
        // state 0 accepts only p0^ω, state 1 nothing, and the edges of state 1 are labeled `t`
        let dpa = prop_dpa(1, "State: 0\n[0] 0 {0}\n[!0] 1 {1}\nState: 1\n[t] 1 {1}");
        assert_eq!(dpa.prefix_partition().len(), 2);
    }
}
