use crate::Color;
use crate::alphabet::Expression;
use crate::representation::{FromTransitions, IntoTransitions, Parts};
use crate::ts::SymbolOf;
use crate::ts::{DenseId, EdgeOf, ForAlphabet, Sproutable, StateId};
use crate::{DTS, NTS};
use std::borrow::Cow;
use std::{cell::RefCell, fmt::Debug};

use crate::ts::{
    Deterministic, DeterministicEdgesFrom, EdgeColor, EdgeExpression, EdgeRef, Pointed, StateIndex,
    TransitionSystem,
};
use crate::{
    alphabet::{Alphabet, Matcher},
    math,
};
use itertools::Itertools;

/// A set of states, stored as a sorted, duplicate-free vector of state indices.
pub struct StateSet<Ts: TransitionSystem>(Vec<Ts::StateIndex>);

impl<Ts: TransitionSystem> Clone for StateSet<Ts> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<Ts: TransitionSystem> Eq for StateSet<Ts> {}

impl<Ts: TransitionSystem> std::hash::Hash for StateSet<Ts> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<Ts: TransitionSystem> StateSet<Ts> {
    /// Restores the invariant that the underlying vector is sorted and duplicate-free.
    fn normalize(&mut self) {
        self.0.sort_unstable();
        self.0.dedup();
    }
}

impl<Ts: TransitionSystem> Extend<Ts::StateIndex> for StateSet<Ts> {
    fn extend<T: IntoIterator<Item = Ts::StateIndex>>(&mut self, iter: T) {
        self.0.extend(iter);
        self.normalize();
    }
}

impl<Ts: TransitionSystem> PartialEq for StateSet<Ts> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<Ts: TransitionSystem> Default for StateSet<Ts> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<Ts: TransitionSystem> IntoIterator for StateSet<Ts> {
    type IntoIter = std::vec::IntoIter<Ts::StateIndex>;
    type Item = Ts::StateIndex;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<Ts: TransitionSystem> FromIterator<Ts::StateIndex> for StateSet<Ts> {
    fn from_iter<T: IntoIterator<Item = Ts::StateIndex>>(iter: T) -> Self {
        let mut set = Self(iter.into_iter().collect());
        set.normalize();
        set
    }
}

impl<Ts: TransitionSystem> StateSet<Ts> {
    pub fn singleton(q: Ts::StateIndex) -> Self {
        Self(vec![q])
    }

    pub fn iter(&self) -> impl Iterator<Item = &'_ Ts::StateIndex> + '_ {
        self.0.iter()
    }
}

impl<Ts: TransitionSystem> std::fmt::Debug for StateSet<Ts> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            write!(f, "∅")
        } else {
            write!(
                f,
                "{{{}}}",
                self.iter().map(|q| format!("{q:?}")).join(", ")
            )
        }
    }
}

/// Represents the subset construction applied to a transition system. This is a deterministic
/// transition system, which resolves the non-determinism by operating on sets of states.
#[derive(Clone)]
pub struct SubsetConstruction<Ts: TransitionSystem> {
    ts: Ts,
    /// Maps the id of a subset to the subset itself.
    states: RefCell<Vec<StateSet<Ts>>>,
    /// Maps a subset to its id, the inverse of `states`.
    ids: RefCell<math::FxIndexMap<StateSet<Ts>, usize>>,
    /// The expression of each symbol of the alphabet, computed once.
    expressions: Vec<EdgeExpression<Ts>>,
}

impl<Ts: TransitionSystem> Deterministic for SubsetConstruction<Ts> {
    fn edge(&self, source: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        let (colorset, mut stateset): (Vec<Ts::EdgeColor>, StateSet<Ts>) = self
            .states
            .borrow()
            .get(source)?
            .iter()
            .flat_map(|q| {
                self.ts
                    .edges_from(*q)
                    .into_iter()
                    .flatten()
                    .filter_map(|tt| {
                        if symbol.matches(tt.expression()) {
                            Some((tt.color().clone(), tt.target()))
                        } else {
                            None
                        }
                    })
            })
            .unzip();
        stateset.normalize();
        let expression = self.expressions.iter().find(|e| symbol.matches(*e))?;

        if let Some(&id) = self.ids.borrow().get(&stateset) {
            return Some(EdgeRef::owned(source, expression, colorset, id));
        }

        let mut states = self.states.borrow_mut();
        let id = states.len();
        self.ids.borrow_mut().insert(stateset.clone(), id);
        states.push(stateset);
        Some(EdgeRef::owned(source, expression, colorset, id))
    }
}

impl<Ts: TransitionSystem> Pointed for SubsetConstruction<Ts> {
    fn initial(&self) -> usize {
        0
    }
}

impl<Ts: TransitionSystem> TransitionSystem for SubsetConstruction<Ts> {
    type StateIndex = usize;

    type StateColor = Vec<Ts::StateColor>;

    type EdgeColor = Vec<Ts::EdgeColor>;

    type EdgesFromIter<'this>
        = DeterministicEdgesFrom<'this, Self>
    where
        Self: 'this;

    type Alphabet = Ts::Alphabet;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(DeterministicEdgesFrom::new(self, state))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.states
            .borrow()
            .get(state)?
            .iter()
            .map(|idx| self.ts.state_color(*idx).map(Cow::into_owned))
            .collect::<Option<Vec<_>>>()
            .map(Cow::Owned)
    }
}

impl<Ts: TransitionSystem> Debug for SubsetConstruction<Ts>
where
    EdgeColor<Ts>: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Subset construction\n{}",
            self.build_transition_table(
                self.reachable_state_indices_from(0),
                |idx, _| format!(
                    "{{{}}}",
                    self.states
                        .borrow()
                        .get(idx)
                        .unwrap()
                        .iter()
                        .map(|q| format!("{q:?}"))
                        .join(", ")
                ),
                |edge| edge.target().to_string()
            )
        )
    }
}

impl<Ts: TransitionSystem> SubsetConstruction<Ts> {
    /// Creates a new subset construction from the given transition system starting from the given index.
    pub fn new_from(ts: Ts, idx: Ts::StateIndex) -> Self {
        Self::from_initial(ts, StateSet::singleton(idx))
    }

    /// Creates a new subset construction from the given transition system starting from the given
    /// indices.
    pub fn new<I: IntoIterator<Item = Ts::StateIndex>>(ts: Ts, iter: I) -> Self {
        Self::from_initial(ts, StateSet::from_iter(iter))
    }

    fn from_initial(ts: Ts, initial: StateSet<Ts>) -> Self {
        Self {
            expressions: ts.alphabet().expression_map().into_values().collect(),
            ids: math::FxIndexMap::from_iter([(initial.clone(), 0)]).into(),
            states: vec![initial].into(),
            ts,
        }
    }
}

/// The problem of determinizing a transition system with the subset construction:
/// [`Determinize::on`] states it for a [`Pointed`] system and [`run`](Determinize::run) explores
/// all reachable subsets eagerly. In contrast to the lazy [`SubsetConstruction`] the result is
/// a stored [`DTS`]. Like in the lazy version, state and edge colors of a subset are the lists of
/// the colors of its members, and a symbol without successors leads to the empty subset, so that
/// the result is complete.
///
/// ```
/// use automata::ts::q;
/// use automata::ts::{Builder, States, operations::Determinize};
///
/// let nts = Builder::default()
///     .default_color(false)
///     .with_transitions([(0, 'a', 0), (0, 'a', 1), (0, 'b', 1), (1, 'b', 1), (1, 'a', 0)])
///     .into_nts_with_initial(0);
/// let determinized = Determinize::on(&nts).run();
/// assert_eq!(determinized.ts().state_count(), 3);
/// assert_eq!(determinized.subsets()[0], vec![q(0)]);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Determinize<'a, Ts>(&'a Ts);

impl<'a, Ts> Determinize<'a, Ts> {
    /// States the problem for the given transition system.
    pub fn on(ts: &'a Ts) -> Self {
        Self(ts)
    }
}

/// The transition system built by [`Determinize`].
pub type DeterminizedTs<Ts> = DTS<
    <Ts as TransitionSystem>::Alphabet,
    Vec<<Ts as TransitionSystem>::StateColor>,
    Vec<<Ts as TransitionSystem>::EdgeColor>,
>;

/// The result of [`Determinize::run`]: the deterministic system, whose initial state is `0`, and
/// the subset of original states that each of its states stands for.
#[derive(Debug, Clone)]
pub struct Determinized<Ts: TransitionSystem> {
    ts: DeterminizedTs<Ts>,
    subsets: Vec<Vec<Ts::StateIndex>>,
}

impl<Ts: TransitionSystem> Determinized<Ts> {
    /// The deterministic transition system, its initial state is `0`.
    pub fn ts(&self) -> &DeterminizedTs<Ts> {
        &self.ts
    }

    /// For each state of [`Self::ts`], the sorted subset of original states it stands for.
    pub fn subsets(&self) -> &[Vec<Ts::StateIndex>] {
        &self.subsets
    }

    /// Merges the edges that lead from a state to the same state with the same colors into one
    /// edge, see [`merge_parallel_edges`]. [`Determinize::run`] does not do this, it labels
    /// the edges by classes of symbols (single atoms for propositional alphabets), of which there
    /// can be very many.
    pub fn merge_edges(self) -> Self
    where
        Ts::EdgeColor: PartialEq,
    {
        Self {
            ts: merge_parallel_edges(self.ts),
            subsets: self.subsets,
        }
    }

    /// Discards the subsets and returns the deterministic transition system.
    pub fn into_dts(self) -> DeterminizedTs<Ts> {
        self.ts
    }

    /// Splits into the deterministic transition system and the subset of each state.
    pub fn into_parts(self) -> (DeterminizedTs<Ts>, Vec<Vec<Ts::StateIndex>>) {
        (self.ts, self.subsets)
    }
}

/// The labels of all edges that are reachable from the initial state of `ts`.
fn reachable_labels<Ts: Pointed>(ts: &Ts) -> Vec<EdgeExpression<Ts>> {
    let mut seen = math::FxIndexSet::default();
    seen.insert(ts.initial());
    let mut labels = Vec::new();
    let mut next = 0;
    while let Some(&q) = seen.get_index(next) {
        next += 1;
        for e in ts.edges_from(q).into_iter().flatten() {
            labels.push(e.expression().clone());
            seen.insert(e.target());
        }
    }
    labels
}

/// Merges the edges of `ts` that lead from a state to the same state with the same color into one
/// edge, which is labeled by the union of their expressions where the alphabet can express it (see
/// [`Expression::union`]). For propositional alphabets this turns many edges, one per atom, into few.
/// Like Spot's `merge_edges` this is a separate step that costs time, but pays off for what
/// follows.
pub fn merge_parallel_edges<A, Q, C>(ts: DTS<A, Q, C>) -> DTS<A, Q, C>
where
    A: Alphabet,
    Q: Color,
    C: Color + PartialEq,
{
    // alphabets whose expressions cannot be united have nothing to merge
    let probe = ts
        .alphabet()
        .universe()
        .next()
        .map(|symbol| ts.alphabet().make_expression(symbol));
    if probe.is_none_or(|expression| expression.union(&expression).is_none()) {
        return ts;
    }
    let Parts {
        alphabet,
        states,
        edges,
        initial: (),
    } = ts.into_transitions();
    let mut merged: Vec<(StateId, A::Expression, C, StateId)> = Vec::new();
    // the merged edges of the current source start here
    let (mut from, mut current) = (None, 0);
    for (source, expression, color, target) in edges {
        if from != Some(source) {
            from = Some(source);
            current = merged.len();
        }
        let same = merged[current..]
            .iter_mut()
            .find(|(_, _, c, t)| *t == target && *c == color);
        match same.and_then(|m| m.1.union(&expression).map(|u| (m, u))) {
            Some((m, union)) => m.1 = union,
            None => merged.push((source, expression, color, target)),
        }
    }
    // the edges of a state are still labeled by disjoint expressions
    crate::ts::Det(NTS::from_transitions(Parts {
        alphabet,
        states,
        edges: merged.into_iter(),
        initial: (),
    }))
}

impl<Ts: Pointed> Determinize<'_, Ts> {
    /// Runs the subset construction from the initial state of the system.
    pub fn run(self) -> Determinized<Ts> {
        let ts = self.0;
        let alphabet = ts.alphabet();
        // Either every symbol of the alphabet, or the classes of symbols that the edge labels
        // reachable from the initial state cannot tell apart (propositional alphabets, see
        // `Alphabet::letter_classes`) together with the classes each label consists of.
        let classes = alphabet.letter_classes(&|| reachable_labels(ts));
        let (symbols, covers): (Vec<_>, _) = match classes {
            Some(classes) => (
                classes.classes.into_iter().map(|e| (None, e)).collect(),
                Some(classes.covers),
            ),
            None => (
                alphabet
                    .universe()
                    .map(|sym| (Some(sym), alphabet.make_expression(sym)))
                    .collect(),
                None,
            ),
        };

        // The edges of a subset are labeled by disjoint expressions, so there is nothing to replace
        // and the overlap check of `DTS` (quadratic for many classes) is skipped.
        let mut out = NTS::for_alphabet(alphabet.clone());
        let mut subsets: Vec<Vec<Ts::StateIndex>> = Vec::new();
        let mut ids: math::FxIndexMap<Vec<Ts::StateIndex>, StateId> = math::FxIndexMap::default();
        let mut discover = |out: &mut NTS<_, _, _>,
                            subsets: &mut Vec<Vec<Ts::StateIndex>>,
                            subset: Vec<Ts::StateIndex>| {
            if let Some(&id) = ids.get(&subset) {
                return id;
            }
            let colors = subset
                .iter()
                .filter_map(|q| ts.state_color(*q).map(Cow::into_owned))
                .collect();
            let id = out.add_state(colors);
            ids.insert(subset.clone(), id);
            subsets.push(subset);
            id
        };
        discover(&mut out, &mut subsets, vec![ts.initial()]);

        // Targets and colors per symbol of the current subset, reused between subsets.
        let mut targets = vec![Vec::new(); symbols.len()];
        let mut colors = vec![Vec::new(); symbols.len()];
        let mut next = 0;
        while next < subsets.len() {
            for i in 0..symbols.len() {
                targets[i].clear();
                colors[i].clear();
            }
            for q in &subsets[next] {
                for e in ts.edges_from(*q).into_iter().flatten() {
                    if let Some(covers) = &covers {
                        for &i in covers.get(e.expression()).map_or(&[][..], Vec::as_slice) {
                            targets[i].push(e.target());
                            colors[i].push(e.color().clone());
                        }
                        continue;
                    }
                    for (i, (sym, _)) in symbols.iter().enumerate() {
                        if sym.is_some_and(|sym| sym.matches(e.expression())) {
                            targets[i].push(e.target());
                            colors[i].push(e.color().clone());
                        }
                    }
                }
            }
            for (i, (_, expression)) in symbols.iter().enumerate() {
                let mut subset = std::mem::take(&mut targets[i]);
                subset.sort_unstable();
                subset.dedup();
                let target = discover(&mut out, &mut subsets, subset);
                out.add_edge((
                    StateId::from_usize(next),
                    expression.clone(),
                    std::mem::take(&mut colors[i]),
                    target,
                ));
            }
            next += 1;
        }
        Determinized {
            ts: crate::ts::Det(out),
            subsets,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::alphabet::Matcher;
    use crate::representation::IntoTransitions;
    use crate::ts::Deterministic;
    use crate::ts::{DenseId, StateId};
    use crate::{NTS, TransitionSystem};
    use crate::{Pointed, States};

    #[test]
    fn determinize_agrees_with_lazy_subset_construction() {
        let nts = NTS::builder()
            .default_color(false)
            .with_transitions([
                (0, 'a', 0),
                (0, 'a', 1),
                (0, 'b', 1),
                (1, 'b', 1),
                (1, 'a', 0),
            ])
            .into_nts_with_initial(0);
        let lazy = (&nts).subset_construction().reachable_part();
        let eager = super::Determinize::on(&nts).run();
        assert_eq!(eager.ts().state_count(), lazy.state_count());
        assert_eq!(eager.subsets().len(), lazy.state_count());
        for (q, subset) in eager.subsets().iter().enumerate() {
            for sym in ['a', 'b'] {
                let expected: std::collections::BTreeSet<_> = subset
                    .iter()
                    .flat_map(|p| nts.edges_from(*p).unwrap())
                    .filter(|e| e.expression().matches(&sym))
                    .map(|e| e.target())
                    .collect();
                let target = eager.ts().successor(StateId::from_usize(q), sym).unwrap();
                assert_eq!(
                    eager.subsets()[target.into_usize()]
                        .iter()
                        .copied()
                        .collect::<std::collections::BTreeSet<_>>(),
                    expected
                );
            }
        }
    }

    #[test]
    fn subset_construction() {
        let nts = NTS::builder()
            .default_color(false)
            .with_transitions([
                (0, 'a', 0),
                (0, 'a', 1),
                (0, 'b', 1),
                (1, 'b', 1),
                (1, 'a', 0),
            ])
            .into_nts_with_initial(0);

        let dts = nts.subset_construction();

        assert_eq!(dts.reachable_state_indices().count(), 3);
        let finite = dts.reachable_part();
        assert_eq!(finite.states().count(), 3);
        assert_eq!(finite.collect::<crate::DTS<_, _, _>>().state_count(), 3);
    }

    #[test]
    fn subset_construction_iterates_edges() {
        use crate::TransitionSystem;
        use crate::ts::Deterministic;
        let nts = NTS::builder()
            .default_color(false)
            .with_transitions([
                (0, 'a', 0),
                (0, 'a', 1),
                (0, 'b', 1),
                (1, 'b', 1),
                (1, 'a', 0),
            ])
            .into_nts_with_initial(0);
        let dts = nts.subset_construction();
        for q in dts.reachable_state_indices().collect::<Vec<_>>() {
            let edges = dts.edges_from(q).unwrap().collect::<Vec<_>>();
            assert_eq!(edges.len(), 2);
            for (e, sym) in edges.iter().zip(['a', 'b']) {
                assert_eq!(dts.edge(q, sym).unwrap().target(), e.target());
            }
        }
    }
}
