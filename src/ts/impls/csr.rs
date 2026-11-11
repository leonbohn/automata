use std::borrow::Cow;
use std::marker::PhantomData;
use std::sync::OnceLock;

use crate::alphabet::{Alphabet, CharAlphabet, Matcher};
use crate::representation::{
    FromTransitions, IntoTransitions, Parts, Renumbering, sprout_from_parts,
};
use crate::{
    Color, TransitionSystem, Void,
    ts::{
        DenseId, Det, Deterministic, EdgeId, EdgeOf, EdgeRef, IdType, LinkedTs, StateId,
        StateIndex, States, SymbolOf, predecessors::PredecessorIterable,
    },
};

/// The sentinel that stands for "no edge" in the target slots of [`CsrTs`].
pub(super) const NONE: u32 = u32::MAX;

/// The incoming edges of the states of a deterministic table in compressed sparse row form: the
/// slots that lead to state `p` are `slots[offsets[p]..offsets[p + 1]]`, in increasing order.
#[derive(Clone, Debug)]
pub(super) struct ReverseCsr {
    offsets: Vec<u32>,
    slots: Vec<u32>,
}

impl ReverseCsr {
    /// Collects the slots of the `n` states whose targets are given, where `NONE` marks an empty
    /// slot, in O(number of slots).
    pub(super) fn build(targets: impl Iterator<Item = u32> + Clone, n: usize) -> Self {
        let mut offsets = vec![0_u32; n + 1];
        for target in targets.clone().filter(|t| *t != NONE) {
            offsets[target as usize + 1] += 1;
        }
        for p in 0..n {
            offsets[p + 1] += offsets[p];
        }
        let mut fill = offsets.clone();
        let mut slots = vec![NONE; offsets[n] as usize];
        for (slot, target) in targets.enumerate() {
            if target != NONE {
                slots[fill[target as usize] as usize] = slot as u32;
                fill[target as usize] += 1;
            }
        }
        Self { offsets, slots }
    }

    /// The slots that lead to state `p`.
    #[inline]
    pub(super) fn to_state(&self, p: usize) -> &[u32] {
        &self.slots[self.offsets[p] as usize..self.offsets[p + 1] as usize]
    }

    /// Panics unless this is the table of the given targets. If `stale` is set, it may also list
    /// slots that no longer lead to the state, as left behind by removing edges.
    pub(super) fn check_against(&self, targets: &[u32], n: usize, stale: bool) {
        assert_eq!(self.offsets.len(), n + 1, "wrong number of offsets");
        for p in 0..n {
            let expected: Vec<_> = (0..targets.len())
                .filter(|slot| targets[*slot] as usize == p)
                .map(|slot| slot as u32)
                .collect();
            let listed: Vec<_> = self
                .to_state(p)
                .iter()
                .copied()
                .filter(|slot| !stale || targets[*slot as usize] as usize == p)
                .collect();
            assert_eq!(listed, expected, "wrong incoming edges of state {p}");
        }
    }
}

/// An edge of a [`CsrTs`], expression, color and target next to each other so that a lookup
/// touches one cache line.
#[derive(Clone)]
struct CsrEdge<E, C> {
    expression: E,
    color: C,
    target: u32,
}

/// A transition system that cannot be changed after it has been built and keeps its edges in
/// compressed sparse row form: the edges are sorted by their source, and `offsets[q]..offsets[q + 1]`
/// is the range of the edges that leave state `q`. It is non-deterministic and works for any
/// [`Alphabet`]; [`Det<CsrTs>`](crate::ts::Det) makes determinism part of the type.
///
/// # Layout
/// One vector of edges (expression, color and target together) and one `u32` offset per state:
/// no tombstones, no links and one allocation instead of one per state. The position of an edge in
/// that vector is its [`EdgeId`]. Within a state, edges keep the order in which they were
/// given.
///
/// Looking up the edge of a state for a symbol scans the (usually short) row of that state, so
/// for small indexed alphabets [`DenseTs`](crate::ts::DenseTs) looks up faster. The incoming edges
/// are not stored: they are collected (as compressed rows of edge ids) the first time
/// [`PredecessorIterable::predecessors`] is called.
///
/// A system is built by collecting another one, see [`IntoTransitions::collect`], by the
/// [`Csr`](crate::ts::Csr) storage or by [`Builder::into_csr`](crate::ts::Builder::into_csr). State
/// indices are consecutive, starting at 0, in the order of the system it was built from.
///
/// # Panics
/// Collecting panics if the system has more than `u32::MAX` edges.
#[derive(Clone)]
pub struct CsrTs<A: Alphabet = CharAlphabet, Q = Void, C = Void> {
    alphabet: A,
    states: Vec<Q>,
    /// `states.len() + 1` entries, the edges of state `q` are `offsets[q]..offsets[q + 1]`.
    offsets: Vec<u32>,
    edges: Vec<CsrEdge<A::Expression, C>>,
    /// The edge ids that lead to each state, built on first use.
    incoming: OnceLock<ReverseCsr>,
}

impl<A: Alphabet, Q: Color, C: Color> CsrTs<A, Q, C> {
    #[inline(always)]
    fn row(&self, state: StateId) -> Option<std::ops::Range<usize>> {
        let q = state.into_usize();
        (q < self.states.len()).then(|| self.offsets[q] as usize..self.offsets[q + 1] as usize)
    }

    #[inline(always)]
    fn edge_at(&self, source: StateId, position: usize) -> EdgeOf<'_, Self> {
        let edge = &self.edges[position];
        EdgeRef::borrowed(
            source,
            &edge.expression,
            &edge.color,
            StateId::from(edge.target),
        )
        .with_id(EdgeId(position as u32))
    }

    /// The position of the first edge of `state` that matches `matcher`.
    #[inline(always)]
    fn position_matching(
        &self,
        state: StateId,
        matcher: impl Matcher<A::Expression>,
    ) -> Option<usize> {
        let row = self.row(state)?;
        let start = row.start;
        self.edges[row]
            .iter()
            .position(|edge| matcher.matches(&edge.expression))
            .map(|i| start + i)
    }

    #[inline]
    fn source_of(&self, position: usize) -> StateId {
        StateId::from_usize(self.offsets.partition_point(|o| *o as usize <= position) - 1)
    }

    fn incoming(&self) -> &ReverseCsr {
        self.incoming.get_or_init(|| {
            ReverseCsr::build(self.edges.iter().map(|e| e.target), self.states.len())
        })
    }

    /// Checks the invariants of the data structure and panics if one is violated: the sizes of
    /// the vectors, that the offsets are non-decreasing and cover all edges, that all targets
    /// exist and, if the incoming edges have been collected, that they are those that lead to each
    /// state, in increasing order.
    ///
    /// # Panics
    /// Panics if one of the invariants is violated.
    pub fn check_consistency(&self) {
        let n = self.states.len();
        let m = self.edges.len();
        assert_eq!(self.offsets.len(), n + 1, "wrong number of offsets");
        assert_eq!(self.offsets[0], 0, "offsets do not start at 0");
        assert_eq!(
            self.offsets[n] as usize, m,
            "offsets do not cover all edges"
        );
        assert!(
            self.offsets.windows(2).all(|w| w[0] <= w[1]),
            "offsets decrease"
        );
        assert!(
            self.edges.iter().all(|e| (e.target as usize) < n),
            "an edge leads to a state that does not exist"
        );
        if let Some(incoming) = self.incoming.get() {
            let targets: Vec<_> = self.edges.iter().map(|e| e.target).collect();
            incoming.check_against(&targets, n, false);
        }
    }
}

impl<A: Alphabet, Q: Color, C: Color> TransitionSystem for CsrTs<A, Q, C> {
    type Alphabet = A;
    type StateIndex = StateId;
    type StateColor = Q;
    type EdgeColor = C;
    type EdgesFromIter<'this>
        = CsrEdgesFrom<'this, A, Q, C>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        let row = self.row(state)?;
        Some(CsrEdgesFrom {
            source: state,
            position: row.start as u32,
            edges: self.edges[row].iter(),
            _ts: PhantomData,
        })
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.states.get(state.into_usize()).map(Cow::Borrowed)
    }

    fn state_bound(&self) -> Option<usize> {
        Some(self.states.len())
    }
}

/// Iterates over the edges that leave a state of a [`CsrTs`], in the order they were given.
pub struct CsrEdgesFrom<'ts, A: Alphabet, Q, C> {
    source: StateId,
    position: u32,
    edges: std::slice::Iter<'ts, CsrEdge<A::Expression, C>>,
    _ts: PhantomData<fn() -> Q>,
}

impl<'ts, A: Alphabet, Q: Color, C: Color> Iterator for CsrEdgesFrom<'ts, A, Q, C> {
    type Item = EdgeOf<'ts, CsrTs<A, Q, C>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let edge = self.edges.next()?;
        let id = EdgeId(self.position);
        self.position += 1;
        Some(
            EdgeRef::borrowed(
                self.source,
                &edge.expression,
                &edge.color,
                StateId::from(edge.target),
            )
            .with_id(id),
        )
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.edges.size_hint()
    }
}

impl<A: Alphabet, Q: Color, C: Color> ExactSizeIterator for CsrEdgesFrom<'_, A, Q, C> {}

/// Iterates over the indices of the states of a [`CsrTs`].
#[derive(Clone, Debug)]
pub struct CsrStateIndices(std::ops::Range<u32>);

impl Iterator for CsrStateIndices {
    type Item = StateId;

    #[inline(always)]
    fn next(&mut self) -> Option<StateId> {
        self.0.next().map(StateId::from)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for CsrStateIndices {}

impl<A: Alphabet, Q: Color, C: Color> States for CsrTs<A, Q, C> {
    type StatesIter<'this>
        = CsrStateIndices
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        CsrStateIndices(0..self.states.len() as u32)
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        index.into_usize() < self.states.len()
    }

    fn state_count(&self) -> usize {
        self.states.len()
    }
}

impl<A: Alphabet, Q: Color, C: Color> Deterministic for Det<CsrTs<A, Q, C>> {
    /// Scans the row of `state` for an edge matching `symbol`.
    #[inline]
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        let position = self.0.position_matching(state, symbol)?;
        Some(self.0.edge_at(state, position))
    }

    #[inline]
    fn successor(
        &self,
        state: StateIndex<Self>,
        symbol: SymbolOf<Self>,
    ) -> Option<StateIndex<Self>> {
        let position = self.0.position_matching(state, symbol)?;
        Some(StateId::from(self.0.edges[position].target))
    }
}

impl<A: Alphabet, Q: Color, C: Color> PredecessorIterable for CsrTs<A, Q, C> {
    type EdgesToIter<'this>
        = CsrEdgesTo<'this, A, Q, C>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        let p = state.into_usize();
        (p < self.states.len()).then(|| CsrEdgesTo {
            ts: self,
            positions: self.incoming().to_state(p).iter(),
        })
    }
}

/// Iterates over the edges that enter a state of a [`CsrTs`], ordered by their position.
pub struct CsrEdgesTo<'ts, A: Alphabet, Q, C> {
    ts: &'ts CsrTs<A, Q, C>,
    positions: std::slice::Iter<'ts, u32>,
}

impl<'ts, A: Alphabet, Q: Color, C: Color> Iterator for CsrEdgesTo<'ts, A, Q, C> {
    type Item = EdgeOf<'ts, CsrTs<A, Q, C>>;

    fn next(&mut self) -> Option<Self::Item> {
        let position = *self.positions.next()? as usize;
        Some(self.ts.edge_at(self.ts.source_of(position), position))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.positions.size_hint()
    }
}

/// Iterator over the states of a [`CsrTs`] that is consumed.
pub struct CsrIntoStates<Q> {
    states: std::iter::Enumerate<std::vec::IntoIter<Q>>,
}

impl<Q> Iterator for CsrIntoStates<Q> {
    type Item = (StateId, Q);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.states.next().map(|(i, c)| (StateId::from_usize(i), c))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.states.size_hint()
    }
}

/// Iterator over the edges of a [`CsrTs`] that is consumed, ordered by source.
pub struct CsrIntoEdges<E, C> {
    offsets: Vec<u32>,
    source: u32,
    position: u32,
    edges: std::vec::IntoIter<CsrEdge<E, C>>,
}

impl<E, C> Iterator for CsrIntoEdges<E, C> {
    type Item = (StateId, E, C, StateId);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let edge = self.edges.next()?;
        while self.offsets[self.source as usize + 1] <= self.position {
            self.source += 1;
        }
        self.position += 1;
        Some((
            StateId::from(self.source),
            edge.expression,
            edge.color,
            StateId::from(edge.target),
        ))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.edges.size_hint()
    }
}

impl<A: Alphabet, Q: Color, C: Color> IntoTransitions for CsrTs<A, Q, C> {
    type Initial = ();
    type IntoStates = CsrIntoStates<Q>;
    type IntoEdges = CsrIntoEdges<A::Expression, C>;

    fn into_transitions(self) -> Parts<A, Self::IntoStates, Self::IntoEdges, ()> {
        Parts {
            alphabet: self.alphabet,
            states: CsrIntoStates {
                states: self.states.into_iter().enumerate(),
            },
            edges: CsrIntoEdges {
                offsets: self.offsets,
                source: 0,
                position: 0,
                edges: self.edges.into_iter(),
            },
            initial: (),
        }
    }
}

impl<A: Alphabet, Q: Color, C: Color> IntoTransitions for Det<CsrTs<A, Q, C>> {
    type Initial = ();
    type IntoStates = CsrIntoStates<Q>;
    type IntoEdges = CsrIntoEdges<A::Expression, C>;

    fn into_transitions(self) -> Parts<A, Self::IntoStates, Self::IntoEdges, ()> {
        self.0.into_transitions()
    }
}

impl<A: Alphabet, Q: Color, C: Color, I: IdType, Init> FromTransitions<I, Init> for CsrTs<A, Q, C> {
    fn from_transitions<S, E>(parts: Parts<A, S, E, Init>) -> Self
    where
        S: Iterator<Item = (I, Q)>,
        E: Iterator<Item = (I, A::Expression, C, I)>,
    {
        let Parts {
            alphabet,
            states: colored,
            edges,
            ..
        } = parts;
        let mut numbering = Renumbering::new();
        let mut states = Vec::with_capacity(colored.size_hint().0);
        for (q, color) in colored {
            numbering.push(q);
            states.push(color);
        }

        let mut edges: Vec<_> = edges
            .map(|(p, e, c, r)| (numbering.get(p), e, c, numbering.get(r)))
            .collect();
        u32::try_from(edges.len()).expect("too many edges for 32 bit ids");
        // stable, so edges of one state keep their order; fast on input that is sorted already
        edges.sort_by_key(|edge| edge.0);

        let mut offsets = vec![0_u32; states.len() + 1];
        let mut sorted = Vec::with_capacity(edges.len());
        for (p, expression, color, r) in edges {
            offsets[p as usize + 1] += 1;
            sorted.push(CsrEdge {
                expression,
                color,
                target: r,
            });
        }
        for q in 0..states.len() {
            offsets[q + 1] += offsets[q];
        }
        Self {
            alphabet,
            states,
            offsets,
            edges: sorted,
            incoming: OnceLock::new(),
        }
    }
}

impl<A: Alphabet, Q: Color, C: Color, I: IdType, Init> FromTransitions<I, Init>
    for Det<CsrTs<A, Q, C>>
{
    /// Edges that overlap with an earlier edge replace it, see [`Sproutable::add_edge`]. Sources
    /// that are deterministic already are not copied again.
    ///
    /// [`Sproutable::add_edge`]: crate::ts::Sproutable::add_edge
    fn from_transitions<S, E>(parts: Parts<A, S, E, Init>) -> Self
    where
        S: Iterator<Item = (I, Q)>,
        E: Iterator<Item = (I, A::Expression, C, I)>,
    {
        let csr = CsrTs::from_transitions(parts);
        if csr.is_deterministic() {
            return Det(csr);
        }
        let linked: Det<LinkedTs<A, Q, C>> = sprout_from_parts(csr.into_transitions());
        Det(CsrTs::from_transitions(linked.into_transitions()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::q;
    use crate::ts::{
        Builder, Csr, DenseTs, ForAlphabet, LinkedTs, Shrinkable, Sproutable, Storage,
    };

    fn dense() -> DenseTs<CharAlphabet, bool, u32> {
        let mut ts = DenseTs::for_alphabet(CharAlphabet::of_size(2));
        let q: Vec<_> = (0..4).map(|i| ts.add_state(i % 2 == 0)).collect();
        ts.add_edge((q[0], 'a', 1u32, q[1]));
        ts.add_edge((q[1], 'a', 2u32, q[2]));
        ts.add_edge((q[2], 'a', 3u32, q[0]));
        ts.add_edge((q[0], 'b', 4u32, q[0]));
        ts.add_edge((q[3], 'b', 5u32, q[0]));
        ts
    }

    #[test]
    fn lookups_and_predecessors() {
        let ts: Det<CsrTs<CharAlphabet, bool, u32>> = (&dense()).collect();
        ts.inner().check_consistency();
        assert_eq!(ts.state_count(), 4);
        assert_eq!(ts.successor(q(0), 'a'), Some(q(1)));
        assert_eq!(ts.successor(q(0), 'b'), Some(q(0)));
        assert_eq!(ts.successor(q(1), 'b'), None);
        assert_eq!(ts.successor(q(0), 'z'), None);
        assert_eq!(ts.successor(q(9), 'a'), None);
        assert_eq!(ts.edge(q(2), 'a').unwrap().id(), Some(EdgeId(3)));
        assert!(*ts.state_color(q(2)).unwrap());
        assert!(ts.edges_from(q(9)).is_none() && ts.predecessors(q(9)).is_none());
        // incoming edges of 0, ordered by position: (0, b), (2, a), (3, b)
        let into_zero: Vec<_> = ts
            .predecessors(q(0))
            .unwrap()
            .map(|e| (e.source(), *e.expression(), *e.color()))
            .collect();
        assert_eq!(
            into_zero,
            vec![(q(0), 'b', 4), (q(2), 'a', 3), (q(3), 'b', 5)]
        );
        ts.inner().check_consistency();
        assert!(!ts.is_complete());
    }

    #[test]
    fn nondeterministic_edges_keep_their_order() {
        let ts = Builder::default()
            .with_state_colors([false, true, false])
            .with_edges([
                (0, 'a', 7u32, 2),
                (1, 'a', 1, 0),
                (0, 'a', 8, 1),
                (0, 'b', 9, 1),
            ])
            .into_csr();
        ts.check_consistency();
        let from_zero: Vec<_> = ts
            .edges_from(q(0))
            .unwrap()
            .map(|e| (*e.expression(), *e.color(), e.target()))
            .collect();
        assert_eq!(
            from_zero,
            vec![('a', 7, q(2)), ('a', 8, q(1)), ('b', 9, q(1))]
        );
        assert!(!ts.is_deterministic());
        // sources of predecessors are found for states without edges, too
        let into_one: Vec<_> = ts.predecessors(q(1)).unwrap().map(|e| e.source()).collect();
        assert_eq!(into_one, vec![q(0), q(0)]);
        assert_eq!(ts.edges_from(q(2)).unwrap().count(), 0);
        // round trip through the parts
        let again: CsrTs<CharAlphabet, bool, u32> = ts.clone().collect();
        assert_eq!(again.edges_from(q(0)).unwrap().count(), 3);
        assert_eq!(again.state_count(), 3);
    }

    #[test]
    fn removed_states_are_dropped_and_the_rest_renumbered() {
        let mut source = dense();
        source.remove_state(q(1));
        let ts: Det<CsrTs<CharAlphabet, bool, u32>> = (&source).collect();
        ts.inner().check_consistency();
        assert_eq!(ts.state_count(), 3);
        // the old states 0, 2, 3 are now 0, 1, 2
        assert_eq!(ts.successor(q(1), 'a'), Some(q(0)));
        assert_eq!(ts.successor(q(2), 'b'), Some(q(0)));
        assert_eq!(ts.successor(q(0), 'a'), None);
    }

    #[test]
    fn empty_system() {
        let ts: CsrTs<CharAlphabet, bool, u32> =
            DenseTs::for_alphabet(CharAlphabet::of_size(2)).collect();
        ts.check_consistency();
        assert_eq!(ts.state_count(), 0);
    }

    #[test]
    fn det_collect_replaces_overlapping_edges() {
        let nts = Builder::default()
            .with_state_colors([false, false])
            .with_edges([(0, 'a', 1u32, 0), (0, 'a', 2, 1)])
            .into_nts();
        let det: Det<CsrTs<CharAlphabet, bool, u32>> = (&nts).collect();
        det.inner().check_consistency();
        assert_eq!(det.successor(q(0), 'a'), Some(q(1)));
        assert_eq!(det.edges_from(q(0)).unwrap().count(), 1);
    }

    #[test]
    fn storage_converts_linked() {
        let mut linked = LinkedTs::for_alphabet(CharAlphabet::of_size(2));
        let (q0, q1) = (linked.add_state(true), linked.add_state(false));
        linked.add_edge((q0, 'a', Void, q1));
        let csr = <Det<Csr> as Storage<_>>::try_from_linked(linked.clone()).unwrap();
        assert_eq!(csr.successor(q(0), 'a'), Some(q(1)));

        linked.add_edge((q0, 'a', Void, q0));
        assert!(<Det<Csr> as Storage<_>>::try_from_linked(linked.clone()).is_err());
        let nondet = <Csr as Storage<_>>::try_from_linked(linked).unwrap();
        assert_eq!(nondet.edges_from(q(0)).unwrap().count(), 2);
    }
}
