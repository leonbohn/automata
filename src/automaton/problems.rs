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

use super::{Automaton, DBA, DFA, DPA};
use crate::alphabet::Expression;
use crate::ts::States;
use crate::ts::connected_components::Scc;
use crate::ts::operations::{Product, ProductIndex};
use crate::ts::{Deterministic, EdgeOf, Pointed, Sccs, StateIndex, SymbolOf, TransitionSystem};
use crate::word::ReducedOmegaWord;
use crate::{Int, math};
use std::borrow::Cow;

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
    /// use automata::{automaton::{DFA, Emptiness}, ts::Builder};
    ///
    /// let ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 1), (1, 'a', 1)])
    ///     .into_dts_with_initial(0);
    /// assert_eq!(Emptiness::of(&DFA::from_ts(&ts, [1])).witness(), Some(vec!['a']));
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
    /// use automata::{automaton::{DFA, Inclusion}, ts::Builder};
    ///
    /// let ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 0)])
    ///     .into_dts_with_initial(0);
    /// let ends_in_a = DFA::from_ts(&ts, [1]);
    /// let anything = DFA::from_ts(&ts, [0, 1]);
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
        product_lasso(self.subset, self.superset, |&c| c, (true, false))
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
        product_lasso(self.left, self.right, |&c| c, (true, false))
            .or_else(|| product_lasso(self.left, self.right, |&c| c, (false, true)))
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
        product_lasso(self.subset, self.superset, |&c| buchi(c), (true, false))
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
        product_lasso(self.left, self.right, |&c| buchi(c), (true, false))
            .or_else(|| product_lasso(self.left, self.right, |&c| buchi(c), (false, true)))
    }

    /// Returns true if and only if the two automata accept the same language.
    pub fn holds(&self) -> bool {
        self.counterexample().is_none()
    }
}

/// A Büchi automaton is a parity automaton with priority 0 on accepting and 1 on other edges.
fn buchi(accepting: bool) -> Int {
    if accepting { 0 } else { 1 }
}

type Priorities = (Int, Int);

/// An edge of a transition system, given by its source, a symbol that takes it and its target.
pub(super) type Through<T> = (StateIndex<T>, SymbolOf<T>, StateIndex<T>);

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

/// An accepted word of an automaton, see [`lasso`].
fn single_lasso<L, S>(
    automaton: &Automaton<L, S>,
    priority: impl Fn(&L::EdgeColor) -> Int,
) -> Option<ReducedOmegaWord<SymbolOf<L>>>
where
    L: Deterministic,
{
    lasso(
        automaton,
        automaton.initial(),
        |c| (priority(c), 0),
        (true, true),
        (0, 0),
    )
}

/// Looks for a word whose run in the product of `left` and `right` has the given acceptance (as
/// seen by the min-even parity condition on `priority`) in both automata.
fn product_lasso<L, R, S>(
    left: &Automaton<L, S>,
    right: &Automaton<R, S>,
    priority: impl Fn(&L::EdgeColor) -> Int + Copy,
    accepted: (bool, bool),
) -> Option<ReducedOmegaWord<SymbolOf<L>>>
where
    L: Deterministic + States,
    R: Deterministic<Alphabet = L::Alphabet, EdgeColor = L::EdgeColor> + States,
{
    let floors = (
        least_priority(left, priority, accepted.0)?,
        least_priority(right, priority, accepted.1)?,
    );
    // Only edges above the floors are explored, which is often much less than the full product.
    let left_priorities = move |c: &L::EdgeColor| (priority(c), 0);
    let right_priorities = move |c: &R::EdgeColor| (priority(c), 0);
    let initial = ProductIndex(left.initial(), right.initial());
    let product = Masked::new(left, &left_priorities, (floors.0, 0))
        .ts_product(Masked::new(right, &right_priorities, (floors.1, 0)))
        .with_initial(initial);
    lasso(
        &product,
        initial,
        |(l, r)| (priority(l), priority(r)),
        accepted,
        (0, 0),
    )
}

/// An ultimately periodic word that leads from `initial` into a cycle of `ts` such that the least
/// first priority on the cycle is even if and only if `accepted.0` and the least second priority
/// is even if and only if `accepted.1`. Edges with priorities below `floor` are ignored.
///
/// This decomposes `ts` into strongly connected components. If all edges of a component (which
/// can be traversed in one cycle) fit, we are done. Otherwise, a cycle must avoid the edges that
/// carry a least priority of the wrong parity, so we remove them and decompose the component
/// again.
fn lasso<T>(
    ts: &T,
    initial: T::StateIndex,
    priorities: impl Fn(&T::EdgeColor) -> Priorities,
    accepted: (bool, bool),
    floor: Priorities,
) -> Option<ReducedOmegaWord<SymbolOf<T>>>
where
    T: TransitionSystem,
{
    let mut found = None;
    search(
        ts,
        vec![initial],
        &priorities,
        accepted,
        floor,
        |scc, through| {
            // A cycle through the edges with the least priorities has exactly these least priorities,
            // as all edges of the component are at least that large. This is much shorter than a
            // cycle that visits the whole component.
            let view = scc.ts();
            let [(from_l, symbol_l, to_l), (from_r, symbol_r, to_r)] = *through;
            let mut cycle = vec![symbol_l];
            if (from_l, symbol_l, to_l) == (from_r, symbol_r, to_r) {
                cycle.extend(view.word_from_to(to_l, from_l)?);
            } else {
                cycle.extend(view.word_from_to(to_l, from_r)?);
                cycle.push(symbol_r);
                cycle.extend(view.word_from_to(to_r, from_l)?);
            }
            found = Some((from_l, cycle));
            Some(())
        },
    );
    let (start, cycle) = found?;
    let spoke = ts.word_from_to(initial, start)?;
    Some(ReducedOmegaWord::ultimately_periodic(spoke, cycle))
}

/// Decomposes the part of `ts` that is reachable from `roots` as described for [`lasso`] and
/// calls `visit` for every component that can be traversed in a good cycle, until it returns
/// `Some`.
pub(super) fn search<T, P>(
    ts: &T,
    roots: Vec<T::StateIndex>,
    priorities: &P,
    accepted: (bool, bool),
    floor: Priorities,
    mut visit: impl for<'v> FnMut(&Scc<'v, Masked<'v, T, P>>, &[Through<T>; 2]) -> Option<()>,
) where
    T: TransitionSystem,
    P: Fn(&T::EdgeColor) -> Priorities,
{
    struct Task<I> {
        floor: Priorities,
        roots: Vec<I>,
        restrict: bool,
    }
    let mut tasks = vec![Task {
        floor,
        roots,
        restrict: false,
    }];
    while let Some(task) = tasks.pop() {
        // built only for tasks that are actually looked at
        let inside: Option<math::FxIndexSet<_>> =
            task.restrict.then(|| task.roots.iter().copied().collect());
        let view = Masked {
            ts,
            priorities,
            floor: task.floor,
            inside: inside.as_ref(),
        };
        let sccs = Sccs::on(&view).from(task.roots).compute();
        let mut good = Vec::new();
        for scc in sccs.sccs_iter().filter(|scc| scc.is_nontransient()) {
            let (mut low_l, mut low_r) = (Int::MAX, Int::MAX);
            let (mut through_l, mut through_r) = (None, None);
            for edge in scc.interior_edges() {
                let (l, r) = priorities(edge.color());
                let through = |edge: &EdgeOf<'_, Masked<'_, T, P>>| {
                    let symbol = edge.expression().symbols().next()?;
                    Some((edge.source(), symbol, edge.target()))
                };
                if l < low_l {
                    low_l = l;
                    through_l = through(&edge);
                }
                if r < low_r {
                    low_r = r;
                    through_r = through(&edge);
                }
            }
            let good_l = low_l.is_multiple_of(2) == accepted.0;
            let good_r = low_r.is_multiple_of(2) == accepted.1;
            if good_l && good_r {
                if let (Some(l), Some(r)) = (through_l, through_r) {
                    good.push((scc, [l, r]));
                }
                continue;
            }
            // Cycles through an edge with a bad least priority are bad, so the edges with that
            // priority are removed. If nothing remains above it, there is no cycle left.
            let mut floor = task.floor;
            if !good_l {
                let Some(next) = low_l.checked_add(1) else {
                    continue;
                };
                floor.0 = next;
            }
            if !good_r {
                let Some(next) = low_r.checked_add(1) else {
                    continue;
                };
                floor.1 = next;
            }
            tasks.push(Task {
                floor,
                roots: scc.state_indices().copied().collect(),
                restrict: true,
            });
        }
        // the smallest components have the shortest cycles
        good.sort_by_key(|(scc, _)| scc.size());
        for (scc, through) in &good {
            if visit(scc, through).is_some() {
                return;
            }
        }
    }
}

/// The part of a transition system that only has edges with priorities above a floor and states
/// from a given set.
pub(super) struct Masked<'a, T: TransitionSystem, P> {
    ts: &'a T,
    priorities: &'a P,
    floor: Priorities,
    inside: Option<&'a math::FxIndexSet<T::StateIndex>>,
}

pub(super) struct MaskedEdges<'a, T: TransitionSystem, P> {
    it: T::EdgesFromIter<'a>,
    mask: &'a Masked<'a, T, P>,
}

impl<'a, T, P> Iterator for MaskedEdges<'a, T, P>
where
    T: TransitionSystem,
    P: Fn(&T::EdgeColor) -> Priorities,
{
    type Item = EdgeOf<'a, T>;
    fn next(&mut self) -> Option<Self::Item> {
        let Masked {
            priorities,
            floor,
            inside,
            ..
        } = self.mask;
        self.it.find(|edge| {
            let (l, r) = priorities(edge.color());
            floor.0 <= l && floor.1 <= r && inside.is_none_or(|set| set.contains(&edge.target()))
        })
    }
}

impl<'a, T: TransitionSystem, P> Masked<'a, T, P> {
    fn new(ts: &'a T, priorities: &'a P, floor: Priorities) -> Self {
        Self {
            ts,
            priorities,
            floor,
            inside: None,
        }
    }
}

impl<'a, T, P> TransitionSystem for Masked<'a, T, P>
where
    T: TransitionSystem,
    P: Fn(&T::EdgeColor) -> Priorities,
{
    type Alphabet = T::Alphabet;
    type StateIndex = T::StateIndex;
    type StateColor = T::StateColor;
    type EdgeColor = T::EdgeColor;
    type EdgesFromIter<'this>
        = MaskedEdges<'this, T, P>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.ts.state_color(state)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(MaskedEdges {
            it: self.ts.edges_from(state)?,
            mask: self,
        })
    }

    fn state_bound(&self) -> Option<usize> {
        self.ts.state_bound()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::Builder;

    #[test]
    fn dfa_problems() {
        let ts = Builder::without_colors()
            .with_edges([(0, 'a', 0), (0, 'b', 1), (1, 'a', 0), (1, 'b', 1)])
            .into_dts_with_initial(0);
        let all = DFA::from_ts(&ts, [0, 1]);
        let some = DFA::from_ts(&ts, [0]);
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
        let looping = DFA::from_ts(&looping, [0]);
        let once = DFA::from_ts(&once, [1, 2]);
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
}
