//! The search for good cycles that acceptance of nondeterministic automata, emptiness and the
//! language comparisons share. A transition system is decomposed into strongly connected
//! components; a component whose edges can be traversed in one good cycle is handed to a visitor,
//! the others are decomposed again with some of their edges masked. What a component is summarized
//! by, when it is good and what is masked otherwise is a [`Decomposition`]:
//!
//! - [`Priorities`] for (pairs of) min-even parity conditions, used by the problems on
//!   deterministic automata. Its mask is a floor of priorities, so masking compares integers.
//! - [`Colors`] for any [`CycleCondition`], used by [`super::Existential`]. Its mask is a set of
//!   edge colors to avoid.

use super::branching::CycleCondition;
use crate::alphabet::Expression;
use crate::math;
use crate::ts::connected_components::Scc;
use crate::ts::{EdgeColor, EdgeOf, Sccs, StateIndex, SymbolOf};
use crate::word::ReducedOmegaWord;
use crate::{Int, TransitionSystem};
use std::borrow::Cow;
use std::hash::{BuildHasher, Hash, Hasher};

/// An edge of a transition system, given by its source, a symbol that takes it and its target.
pub(crate) type Through<T> = (StateIndex<T>, SymbolOf<T>, StateIndex<T>);

/// What [`Decomposition::verdict`] decides about a component.
pub(crate) enum Verdict<T: TransitionSystem, M> {
    /// The component has a good cycle through these edges (a cycle in a component can visit all
    /// of them, and visiting them is enough for it to be good).
    Accept(Vec<Through<T>>),
    /// Good cycles avoid what one of these masks removes, each is decomposed further. No mask
    /// means there is no good cycle.
    Refine(Vec<M>),
}

/// How [`search`] judges a component, see the [module](self) documentation.
pub(crate) trait Decomposition<T: TransitionSystem> {
    /// What is removed from a component. The default removes nothing.
    type Mask: Clone + Default + Eq + Hash;
    /// What is collected about the edges of a component.
    type Summary;
    /// Whether a component can be reached again under different masks, so that tasks have to
    /// be deduplicated. This is false if [`Self::verdict`] never refines into several masks.
    const BRANCHES: bool;
    /// Whether an edge with this color stays under the mask.
    fn keeps(&self, mask: &Self::Mask, color: &EdgeColor<T>) -> bool;
    /// The summary of a component without edges.
    fn summary(&self) -> Self::Summary;
    /// Adds an interior edge of a component to its summary.
    fn add(&self, summary: &mut Self::Summary, edge: &EdgeOf<'_, T>);
    /// Decides about a component that was decomposed under `mask`.
    fn verdict(&self, summary: Self::Summary, mask: &Self::Mask) -> Verdict<T, Self::Mask>;
}

/// The edge as a [`Through`], if some symbol takes it.
fn through<T: TransitionSystem>(edge: &EdgeOf<'_, T>) -> Option<Through<T>> {
    Some((
        edge.source(),
        edge.expression().symbols().next()?,
        edge.target(),
    ))
}

/// Decomposes the part of `ts` that is reachable from `roots` and calls `visit` for every
/// component that has a good cycle according to `decomposition`, until it returns `Some`. Among
/// the good components found together, the smaller ones come first (their cycles are shorter).
pub(crate) fn search<T, D, R>(
    ts: &T,
    roots: Vec<StateIndex<T>>,
    decomposition: &D,
    mut visit: impl for<'v> FnMut(&Scc<'v, Masked<'v, T, D>>, &[Through<T>]) -> Option<R>,
) -> Option<R>
where
    T: TransitionSystem,
    D: Decomposition<T>,
{
    struct Task<I, M> {
        roots: Vec<I>,
        mask: M,
        restrict: bool,
    }
    let mut seen = math::FxIndexSet::default();
    let mut tasks = vec![Task {
        roots,
        mask: D::Mask::default(),
        restrict: false,
    }];
    while let Some(task) = tasks.pop() {
        // built only for tasks that are actually looked at
        let inside: Option<math::FxIndexSet<_>> =
            task.restrict.then(|| task.roots.iter().copied().collect());
        let view = Masked {
            ts,
            decomposition,
            mask: &task.mask,
            inside: inside.as_ref(),
        };
        let sccs = Sccs::on(&view).from(task.roots).compute();
        let mut good = Vec::new();
        for scc in sccs.sccs_iter().filter(|scc| scc.is_nontransient()) {
            let mut summary = decomposition.summary();
            for edge in scc.interior_edges() {
                decomposition.add(&mut summary, &edge);
            }
            match decomposition.verdict(summary, &task.mask) {
                Verdict::Accept(through) => good.push((scc, through)),
                Verdict::Refine(masks) => {
                    let mut states: Vec<_> = scc.state_indices().copied().collect();
                    if D::BRANCHES {
                        states.sort_unstable();
                    }
                    for mask in masks {
                        if D::BRANCHES && !seen.insert((states.clone(), mask.clone())) {
                            continue;
                        }
                        tasks.push(Task {
                            roots: states.clone(),
                            mask,
                            restrict: true,
                        });
                    }
                }
            }
        }
        good.sort_by_key(|(scc, _)| scc.size());
        for (scc, through) in &good {
            if let Some(found) = visit(scc, through) {
                return Some(found);
            }
        }
    }
    None
}

/// An ultimately periodic word that leads from `initial` into a good cycle of `ts`: a path to the
/// first good component that [`search`] finds, then a cycle through the edges it names.
pub(crate) fn lasso<T, D>(
    ts: &T,
    initial: StateIndex<T>,
    decomposition: &D,
) -> Option<ReducedOmegaWord<SymbolOf<T>>>
where
    T: TransitionSystem,
    D: Decomposition<T>,
{
    let (start, cycle) = search(ts, vec![initial], decomposition, |scc, through| {
        let view = scc.ts();
        let start = through.first()?.0;
        let (mut cycle, mut at) = (Vec::new(), start);
        for &(from, symbol, to) in through {
            cycle.extend(view.word_from_to(at, from)?);
            cycle.push(symbol);
            at = to;
        }
        cycle.extend(view.word_from_to(at, start)?);
        Some((start, cycle))
    })?;
    let spoke = ts.word_from_to(initial, start)?;
    Some(ReducedOmegaWord::ultimately_periodic(spoke, cycle))
}

/// Pairs of min-even parity conditions, given by `priorities`: a cycle is good if its least first
/// priority is even if and only if `accepted.0`, and likewise for the second. A single condition
/// uses a constant second priority. The mask is a floor below which priorities are removed: a
/// cycle through a least priority of the wrong parity is bad, so a component without a good
/// cycle through all edges continues without its least priority.
pub(crate) struct Priorities<P> {
    pub(crate) priorities: P,
    pub(crate) accepted: (bool, bool),
}

impl<T, P> Decomposition<T> for Priorities<P>
where
    T: TransitionSystem,
    P: Fn(&EdgeColor<T>) -> (Int, Int),
{
    type Mask = (Int, Int);
    /// The least priority of each side, with an edge that carries it.
    type Summary = [(Int, Option<Through<T>>); 2];
    const BRANCHES: bool = false;

    #[inline]
    fn keeps(&self, floor: &(Int, Int), color: &EdgeColor<T>) -> bool {
        let (l, r) = (self.priorities)(color);
        floor.0 <= l && floor.1 <= r
    }

    fn summary(&self) -> Self::Summary {
        [(Int::MAX, None), (Int::MAX, None)]
    }

    #[inline]
    fn add(&self, [left, right]: &mut Self::Summary, edge: &EdgeOf<'_, T>) {
        let (l, r) = (self.priorities)(edge.color());
        if l < left.0 {
            *left = (l, through::<T>(edge));
        }
        if r < right.0 {
            *right = (r, through::<T>(edge));
        }
    }

    fn verdict(&self, summary: Self::Summary, floor: &(Int, Int)) -> Verdict<T, (Int, Int)> {
        let [(low_l, through_l), (low_r, through_r)] = summary;
        let good_l = low_l.is_multiple_of(2) == self.accepted.0;
        let good_r = low_r.is_multiple_of(2) == self.accepted.1;
        if good_l && good_r {
            // A cycle through the edges with the least priorities has exactly these least
            // priorities, as all edges of the component are at least that large.
            return match (through_l, through_r) {
                (Some(l), Some(r)) if l == r => Verdict::Accept(vec![l]),
                (Some(l), Some(r)) => Verdict::Accept(vec![l, r]),
                _ => Verdict::Refine(Vec::new()),
            };
        }
        let mut floor = *floor;
        for (good, low, side) in [(good_l, low_l, &mut floor.0), (good_r, low_r, &mut floor.1)] {
            if !good {
                // If nothing remains above it, there is no cycle left.
                let Some(next) = low.checked_add(1) else {
                    return Verdict::Refine(Vec::new());
                };
                *side = next;
            }
        }
        Verdict::Refine(vec![floor])
    }
}

/// Any [`CycleCondition`]: a component is good if its set of edge colors satisfies the condition,
/// otherwise it is decomposed without the colors of each alternative of
/// [`CycleCondition::avoid`].
pub(crate) struct Colors<'c, C>(pub(crate) &'c C);

/// A set of colors to avoid. Equality and hashing do not depend on the order of insertion.
#[derive(Clone)]
pub(crate) struct ColorMask<C>(math::FxIndexSet<C>);

impl<C> Default for ColorMask<C> {
    fn default() -> Self {
        Self(math::FxIndexSet::default())
    }
}

impl<C: Hash + Eq> PartialEq for ColorMask<C> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<C: Hash + Eq> Eq for ColorMask<C> {}

impl<C: Hash> Hash for ColorMask<C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let combined = self.0.iter().fold(0u64, |acc, color| {
            acc.wrapping_add(math::FxBuildHasher.hash_one(color))
        });
        state.write_u64(combined);
        state.write_usize(self.0.len());
    }
}

impl<T, C> Decomposition<T> for Colors<'_, C>
where
    T: TransitionSystem,
    C: CycleCondition<Color = EdgeColor<T>>,
    EdgeColor<T>: Hash + Eq,
{
    type Mask = ColorMask<EdgeColor<T>>;
    /// The colors of the component, with one edge for each.
    type Summary = (math::FxIndexSet<EdgeColor<T>>, Vec<Through<T>>);
    const BRANCHES: bool = true;

    #[inline]
    fn keeps(&self, mask: &Self::Mask, color: &EdgeColor<T>) -> bool {
        mask.0.is_empty() || !mask.0.contains(color)
    }

    fn summary(&self) -> Self::Summary {
        (math::FxIndexSet::default(), Vec::new())
    }

    fn add(&self, (colors, throughs): &mut Self::Summary, edge: &EdgeOf<'_, T>) {
        if !colors.contains(edge.color())
            && let Some(through) = through::<T>(edge)
        {
            colors.insert(edge.color().clone());
            throughs.push(through);
        }
    }

    fn verdict(
        &self,
        (colors, throughs): Self::Summary,
        mask: &Self::Mask,
    ) -> Verdict<T, Self::Mask> {
        if colors.is_empty() {
            return Verdict::Refine(Vec::new());
        }
        if self.0.satisfied_by(&colors) {
            return Verdict::Accept(throughs);
        }
        let masks = self
            .0
            .avoid(&colors)
            .into_iter()
            .filter_map(|more| {
                let mut avoid = mask.clone();
                avoid.0.extend(more);
                // a mask has to remove a color of the component, otherwise nothing changes
                colors
                    .iter()
                    .any(|color| avoid.0.contains(color))
                    .then_some(avoid)
            })
            .collect();
        Verdict::Refine(masks)
    }
}

/// The part of a transition system that a [`Decomposition`] keeps under a mask, optionally
/// restricted to a set of states.
pub(crate) struct Masked<'a, T: TransitionSystem, D: Decomposition<T>> {
    ts: &'a T,
    decomposition: &'a D,
    mask: &'a D::Mask,
    inside: Option<&'a math::FxIndexSet<StateIndex<T>>>,
}

/// The edges of a [`Masked`] view that start in a state.
pub(crate) struct MaskedEdges<'a, T: TransitionSystem, D: Decomposition<T>> {
    it: T::EdgesFromIter<'a>,
    view: &'a Masked<'a, T, D>,
}

impl<'a, T: TransitionSystem, D: Decomposition<T>> Iterator for MaskedEdges<'a, T, D> {
    type Item = EdgeOf<'a, T>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let Masked {
            decomposition,
            mask,
            inside,
            ..
        } = self.view;
        self.it.find(|edge| {
            decomposition.keeps(mask, edge.color())
                && inside.is_none_or(|set| set.contains(&edge.target()))
        })
    }
}

impl<'a, T: TransitionSystem, D: Decomposition<T>> TransitionSystem for Masked<'a, T, D> {
    type Alphabet = T::Alphabet;
    type StateIndex = T::StateIndex;
    type StateColor = T::StateColor;
    type EdgeColor = T::EdgeColor;
    type EdgesFromIter<'this>
        = MaskedEdges<'this, T, D>
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
            view: self,
        })
    }

    fn state_bound(&self) -> Option<usize> {
        self.ts.state_bound()
    }
}
