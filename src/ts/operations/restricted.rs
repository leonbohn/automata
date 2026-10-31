use crate::representation::{IntoTransitions, Parts};
use crate::ts::EdgeOf;
use crate::ts::SymbolOf;

use crate::ts::States;
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{Deterministic, EdgeColor, IdType, StateIndex};
use crate::{Congruence, Pointed, TransitionSystem};
use std::borrow::Cow;
use std::collections::BTreeSet;
use std::marker::PhantomData;
use std::sync::Arc;

/// Abstracts the filtering of a transition system's state indices. This trait is implemented by
/// functions which take a state index and return a boolean value indicating whether the state index
/// should be filtered out or not. It is also implemented by [`crate::ts::StateSet`] and [`BTreeSet`], which keep exactly the
/// state indices that they contain. A `StateSet` answers in constant time, a `Vec` would need a
/// linear scan per edge and is therefore not accepted.
pub trait StateIndexFilter<Idx: IdType> {
    /// This method is called to check whether an index should be present in a filtered transition
    /// system or not. Any index for which the function returns `true`, will be present, while all those
    /// for which the function returns `false` are masked out.
    fn is_unmasked(&self, idx: Idx) -> bool;

    /// The counterpart to [`Self::is_unmasked`]. This method is called to check whether an index
    /// should be masked out or not. Any index for which the function returns `true`, will be masked
    /// out, while all those for which the function returns `false` are present.
    fn is_masked(&self, idx: Idx) -> bool {
        !self.is_unmasked(idx)
    }
}

impl<Idx, F> StateIndexFilter<Idx> for F
where
    Idx: IdType,
    F: Fn(Idx) -> bool,
{
    #[inline(always)]
    fn is_unmasked(&self, idx: Idx) -> bool {
        (self)(idx)
    }
}

impl<Idx> StateIndexFilter<Idx> for crate::ts::StateSet<Idx>
where
    Idx: IdType,
{
    #[inline(always)]
    fn is_unmasked(&self, idx: Idx) -> bool {
        self.contains(&idx)
    }
}

impl<Idx> StateIndexFilter<Idx> for BTreeSet<Idx>
where
    Idx: IdType,
{
    #[inline(always)]
    fn is_unmasked(&self, idx: Idx) -> bool {
        self.contains(&idx)
    }
}

/// Restricts a transition system to a subset of its state indices, which is defined by a filter
/// function.
#[derive(Debug, Clone)]
pub struct RestrictByStateIndex<Ts: TransitionSystem, F> {
    ts: Ts,
    filter: F,
}

impl<Ts: TransitionSystem, F> TransitionSystem for RestrictByStateIndex<Ts, F>
where
    F: StateIndexFilter<Ts::StateIndex>,
{
    type StateIndex = Ts::StateIndex;

    type EdgeColor = Ts::EdgeColor;

    type StateColor = Ts::StateColor;

    type EdgesFromIter<'this>
        = RestrictedEdgesFromIter<'this, Ts, F>
    where
        Self: 'this;

    type Alphabet = Ts::Alphabet;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts().alphabet()
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        if (self.filter()).is_masked(state) {
            return None;
        }
        self.ts().state_color(state)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        if !(self.filter()).is_unmasked(state) {
            return None;
        }
        self.ts()
            .edges_from(state)
            .map(|iter| RestrictedEdgesFromIter::new(iter, self.filter()))
    }

    fn state_bound(&self) -> Option<usize> {
        self.ts().state_bound()
    }
}

impl<Ts: States, F> States for RestrictByStateIndex<Ts, F>
where
    F: StateIndexFilter<Ts::StateIndex>,
{
    type StatesIter<'this>
        = RestrictedStateIndices<'this, Ts, F>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        RestrictedStateIndices {
            it: self.ts().states(),
            filter: &self.filter,
        }
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        self.filter.is_unmasked(index) && self.ts().contains_state(index)
    }
}

/// Iterator over the states of a [`RestrictByStateIndex`] that is consumed.
pub struct RestrictedIntoStates<I, F> {
    it: I,
    filter: Arc<F>,
}

impl<Idx: IdType, Q, I: Iterator<Item = (Idx, Q)>, F: StateIndexFilter<Idx>> Iterator
    for RestrictedIntoStates<I, F>
{
    type Item = (Idx, Q);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.it.find(|(q, _)| self.filter.is_unmasked(*q))
    }
}

/// Iterator over the edges of a [`RestrictByStateIndex`] that is consumed, it only yields edges
/// between unmasked states.
pub struct RestrictedIntoEdges<I, F> {
    it: I,
    filter: Arc<F>,
}

impl<Idx: IdType, E, C, I: Iterator<Item = (Idx, E, C, Idx)>, F: StateIndexFilter<Idx>> Iterator
    for RestrictedIntoEdges<I, F>
{
    type Item = (Idx, E, C, Idx);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.it
            .find(|(p, _, _, r)| self.filter.is_unmasked(*p) && self.filter.is_unmasked(*r))
    }
}

impl<Ts: IntoTransitions, F> IntoTransitions for RestrictByStateIndex<Ts, F>
where
    F: StateIndexFilter<Ts::StateIndex>,
{
    type Initial = Ts::Initial;
    type IntoStates = RestrictedIntoStates<Ts::IntoStates, F>;
    type IntoEdges = RestrictedIntoEdges<Ts::IntoEdges, F>;

    fn into_transitions(
        self,
    ) -> Parts<Self::Alphabet, Self::IntoStates, Self::IntoEdges, Self::Initial> {
        let Parts {
            alphabet,
            states,
            edges,
            initial,
        } = self.ts.into_transitions();
        let filter = Arc::new(self.filter);
        Parts {
            alphabet,
            states: RestrictedIntoStates {
                it: states,
                filter: filter.clone(),
            },
            edges: RestrictedIntoEdges { it: edges, filter },
            initial,
        }
    }
}

/// Iterator over the state indices of a transition system that are restricted by a filter function.
pub struct RestrictByStateIndexIter<'a, Ts: States + 'a, F> {
    filter: &'a F,
    it: Ts::StatesIter<'a>,
}

impl<Ts, F> Iterator for RestrictByStateIndexIter<'_, Ts, F>
where
    Ts: States,
    F: StateIndexFilter<Ts::StateIndex>,
{
    type Item = Ts::StateIndex;
    fn next(&mut self) -> Option<Self::Item> {
        self.it.find(|idx| self.filter.is_unmasked(*idx))
    }
}

impl<'a, Ts: States, F> RestrictByStateIndexIter<'a, Ts, F> {
    /// Creates a new iterator over the state indices of a transition system that are restricted by a
    /// filter function.
    pub fn new(filter: &'a F, it: Ts::StatesIter<'a>) -> Self {
        Self { filter, it }
    }
}

impl<Ts: TransitionSystem + Pointed, F> Pointed for RestrictByStateIndex<Ts, F>
where
    F: StateIndexFilter<Ts::StateIndex>,
{
    /// # Panics
    /// Panics if the filter excludes the initial state of the underlying system.
    fn initial(&self) -> Self::StateIndex {
        let initial = self.ts.initial();
        assert!(
            (self.filter).is_unmasked(initial),
            "initial state is filtered out"
        );
        initial
    }
}

impl<Ts: TransitionSystem, F> RestrictByStateIndex<Ts, F> {
    /// Restricts `ts` to those states whose index satisfies the `filter`.
    pub fn new(ts: Ts, filter: F) -> Self {
        Self { ts, filter }
    }
    /// Consumes `self` and returns the underlying transition system and the filter.
    pub fn into_parts(self) -> (Ts, F) {
        (self.ts, self.filter)
    }

    /// Returns a reference to the filter that decides which states are kept.
    pub fn filter(&self) -> &F {
        &self.filter
    }

    /// Returns a reference to the underlying transition system.
    pub fn ts(&self) -> &Ts {
        &self.ts
    }
}

/// Adapts an iterator of state indices to filter out those that are masked
/// by a filter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RestrictedStateIndices<'a, Ts: States + 'a, F> {
    filter: &'a F,
    it: Ts::StatesIter<'a>,
}

impl<'a, Ts: States + 'a, F> Iterator for RestrictedStateIndices<'a, Ts, F>
where
    F: StateIndexFilter<Ts::StateIndex>,
{
    type Item = StateIndex<Ts>;
    fn next(&mut self) -> Option<Self::Item> {
        self.it.find(|q| self.filter.is_unmasked(*q))
    }
}

/// Iterator over the edges of a transition system that are restricted by a filter function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RestrictedEdgesFromIter<'a, Ts: TransitionSystem + 'a, F> {
    filter: &'a F,
    it: Ts::EdgesFromIter<'a>,
}

impl<'a, Ts: TransitionSystem + 'a, F> RestrictedEdgesFromIter<'a, Ts, F> {
    /// Wraps an iterator over edges, keeping only those whose target satisfies the `filter`.
    pub fn new(it: Ts::EdgesFromIter<'a>, filter: &'a F) -> Self {
        Self { filter, it }
    }
}

impl<'a, Ts: TransitionSystem + 'a, F> Iterator for RestrictedEdgesFromIter<'a, Ts, F>
where
    F: StateIndexFilter<Ts::StateIndex>,
{
    type Item = EdgeOf<'a, Ts>;
    fn next(&mut self) -> Option<Self::Item> {
        self.it
            .by_ref()
            .find(|edge| (self.filter).is_unmasked(edge.target()))
    }
}

/// Iterator over the predecessors in a transition system that are restricted by a filter function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RestrictedEdgesToIter<'a, Ts: PredecessorIterable + 'a, F> {
    filter: &'a F,
    it: Ts::EdgesToIter<'a>,
}

impl<'a, Ts: PredecessorIterable + 'a, F> Iterator for RestrictedEdgesToIter<'a, Ts, F>
where
    F: StateIndexFilter<Ts::StateIndex>,
{
    type Item = EdgeOf<'a, Ts>;
    fn next(&mut self) -> Option<Self::Item> {
        self.it
            .by_ref()
            .find(|edge| (self.filter).is_unmasked(edge.source()))
    }
}

impl<'a, Ts: PredecessorIterable + 'a, F> RestrictedEdgesToIter<'a, Ts, F> {
    /// Wraps an iterator over incoming edges, keeping only those whose source satisfies the `filter`.
    pub fn new(it: Ts::EdgesToIter<'a>, filter: &'a F) -> Self {
        Self { filter, it }
    }
}

/// Takes a transition system and restricts the the possible edge colors. For this, we assume that the colors
/// can be ordered and we are given a minimal and maximal allowed color.
#[derive(Clone, Debug)]
pub struct EdgeColorRestricted<D: TransitionSystem> {
    ts: D,
    min: D::EdgeColor,
    max: D::EdgeColor,
}

impl<D: Congruence> Pointed for EdgeColorRestricted<D>
where
    EdgeColor<D>: Ord,
{
    fn initial(&self) -> Self::StateIndex {
        self.ts.initial()
    }
}

impl<D: TransitionSystem> TransitionSystem for EdgeColorRestricted<D>
where
    EdgeColor<D>: Ord,
{
    type StateIndex = D::StateIndex;

    type StateColor = D::StateColor;

    type EdgeColor = D::EdgeColor;

    type EdgesFromIter<'this>
        = ColorRestrictedEdgesFrom<'this, D>
    where
        Self: 'this;

    type Alphabet = D::Alphabet;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts().alphabet()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        let min = self.min.clone();
        let max = self.max.clone();
        Some(ColorRestrictedEdgesFrom {
            min,
            max,
            _phantom: PhantomData,
            it: self.ts().edges_from(state)?,
        })
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.ts().state_color(state)
    }

    fn state_bound(&self) -> Option<usize> {
        self.ts().state_bound()
    }
}

impl<D: States> States for EdgeColorRestricted<D>
where
    EdgeColor<D>: Ord,
{
    type StatesIter<'this>
        = D::StatesIter<'this>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        self.ts().states()
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        self.ts().contains_state(index)
    }

    fn state_count(&self) -> usize {
        self.ts().state_count()
    }
}

impl<D: PredecessorIterable<EdgeColor = usize>> PredecessorIterable for EdgeColorRestricted<D> {
    type EdgesToIter<'this>
        = ColorRestrictedEdgesTo<'this, &'this D>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Some(ColorRestrictedEdgesTo::new(
            self.ts().predecessors(state)?,
            self.min,
            self.max,
        ))
    }
}

impl<D> Deterministic for EdgeColorRestricted<D>
where
    D: Deterministic,
    EdgeColor<D>: Ord,
{
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        self.ts()
            .edge(state, symbol)
            .filter(|t| *t.color() <= self.max && self.min <= *t.color())
    }
}

/// Adapted iterator giving the edges from a state in a transition system that are restricted by a
/// color range. See [`EdgeColorRestricted`] for more information.
pub struct ColorRestrictedEdgesFrom<'a, D: TransitionSystem> {
    _phantom: PhantomData<&'a D>,
    it: D::EdgesFromIter<'a>,
    min: D::EdgeColor,
    max: D::EdgeColor,
}

impl<'a, D: TransitionSystem> Iterator for ColorRestrictedEdgesFrom<'a, D>
where
    EdgeColor<D>: Ord,
{
    type Item = EdgeOf<'a, D>;

    fn next(&mut self) -> Option<Self::Item> {
        self.it
            .find(|t| *t.color() <= self.max && self.min <= *t.color())
    }
}

/// Adapted iterator giving the edges to a state in a transition system that are restricted by a
/// color range. See [`EdgeColorRestricted`] for more information.
pub struct ColorRestrictedEdgesTo<'a, D: PredecessorIterable> {
    _phantom: PhantomData<&'a D>,
    it: D::EdgesToIter<'a>,
    min: D::EdgeColor,
    max: D::EdgeColor,
}

impl<'a, D: PredecessorIterable> ColorRestrictedEdgesTo<'a, D> {
    /// Creates a new instance of the iterator.
    pub fn new(it: D::EdgesToIter<'a>, min: D::EdgeColor, max: D::EdgeColor) -> Self {
        Self {
            _phantom: PhantomData,
            it,
            min,
            max,
        }
    }
}

impl<'a, D: PredecessorIterable> Iterator for ColorRestrictedEdgesTo<'a, D>
where
    EdgeColor<D>: Ord,
{
    type Item = EdgeOf<'a, D>;

    fn next(&mut self) -> Option<Self::Item> {
        self.it
            .find(|t| *t.color() <= self.max && self.min <= *t.color())
    }
}

impl<D: TransitionSystem> EdgeColorRestricted<D> {
    /// Returns a reference to the underlying transition system.
    pub fn ts(&self) -> &D {
        &self.ts
    }
    /// Creates a new instance for a given transition system and a color range (as specified by the `min` and `max`
    /// allowed color)
    pub fn new(ts: D, min: D::EdgeColor, max: D::EdgeColor) -> Self {
        Self { ts, min, max }
    }
}

#[cfg(test)]
mod tests {
    use crate::TransitionSystem;
    use crate::representation::IntoTransitions;
    use crate::ts::Builder;

    #[test]
    fn restrict_ts_by_state_index() {
        let dfa = Builder::without_edge_colors()
            .with_state_colors([false, false, true])
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 0),
                (1, 'a', 2),
                (1, 'b', 1),
                (2, 'a', 0),
                (2, 'b', 2),
            ])
            .into_dfa(0);

        assert!(dfa.accepts("aa"));

        let restricted = dfa.restrict_state_indices(|idx| idx != 2);
        assert!(
            !restricted
                .erase_edge_colors()
                .collect::<crate::automaton::DFA>()
                .accepts("aa")
        );
    }

    #[test]
    fn restricting_by_a_state_set() {
        use crate::ts::{Builder, Deterministic, StateSet, States};
        let ts = Builder::without_colors()
            .with_edges([(0, 'a', 1), (1, 'a', 2), (2, 'a', 0)])
            .into_dts_with_initial(0);
        let keep: StateSet<u32> = [0, 1].into_iter().collect();
        let restricted = (&ts).restrict_state_indices(keep);
        assert_eq!(restricted.reached_state("a"), Some(1));
        assert_eq!(restricted.reached_state("aa"), None);
        assert!(restricted.contains_state(1));
        assert!(!restricted.contains_state(2));
    }
}
