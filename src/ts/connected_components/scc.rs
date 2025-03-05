use std::{cell::OnceCell, collections::BTreeSet, fmt::Debug, hash::Hash};

use crate::congruence::MinimalRepresentative;
use crate::core::{
    alphabet::Expression,
    math,
    math::{OrderedSet, Set},
};
use crate::ts::{EdgeColor, EdgeExpression, IsEdge, StateIndex, SymbolOf};
use crate::{Pointed, TransitionSystem};
use itertools::Itertools;

type InteriorEdgeSet<Ts> = Set<(
    <Ts as TransitionSystem>::StateIndex,
    EdgeExpression<Ts>,
    <Ts as TransitionSystem>::EdgeColor,
    <Ts as TransitionSystem>::StateIndex,
)>;
type InteriorTransitionSet<Ts> = Set<(
    <Ts as TransitionSystem>::StateIndex,
    SymbolOf<Ts>,
    <Ts as TransitionSystem>::EdgeColor,
    <Ts as TransitionSystem>::StateIndex,
)>;
type BorderEdgeSet<Ts> = Set<(
    <Ts as TransitionSystem>::StateIndex,
    EdgeExpression<Ts>,
    <Ts as TransitionSystem>::EdgeColor,
    <Ts as TransitionSystem>::StateIndex,
)>;
type BorderTransitionSet<Ts> = Set<(
    <Ts as TransitionSystem>::StateIndex,
    SymbolOf<Ts>,
    <Ts as TransitionSystem>::EdgeColor,
    <Ts as TransitionSystem>::StateIndex,
)>;

/// Represents a strongly connected component of a transition system.
#[derive(Clone)]
pub struct Scc<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    states: BTreeSet<Ts::StateIndex>,
    interior_transitions: OnceCell<InteriorTransitionSet<Ts>>,
    interior_edges: OnceCell<InteriorEdgeSet<Ts>>,
    edge_colors: OnceCell<Set<Ts::EdgeColor>>,
    minimal_representative: OnceCell<Option<MinimalRepresentative<Ts>>>,
    border_edges: OnceCell<BorderEdgeSet<Ts>>,
    border_transitions: OnceCell<BorderTransitionSet<Ts>>,
}

impl<Ts: TransitionSystem> IntoIterator for Scc<'_, Ts> {
    type IntoIter = std::collections::btree_set::IntoIter<Ts::StateIndex>;
    type Item = Ts::StateIndex;
    fn into_iter(self) -> Self::IntoIter {
        self.states.into_iter()
    }
}

impl<Ts: TransitionSystem> std::ops::Deref for Scc<'_, Ts> {
    type Target = BTreeSet<Ts::StateIndex>;

    fn deref(&self) -> &Self::Target {
        &self.states
    }
}

impl<T: TransitionSystem> PartialEq<Vec<StateIndex<T>>> for Scc<'_, T> {
    fn eq(&self, other: &Vec<StateIndex<T>>) -> bool {
        self.states.iter().sorted().eq(other.iter().sorted())
    }
}

impl<Ts: TransitionSystem> PartialEq for Scc<'_, Ts> {
    fn eq(&self, other: &Self) -> bool {
        self.states == other.states
    }
}
impl<Ts: TransitionSystem> Eq for Scc<'_, Ts> {}

impl<Ts: TransitionSystem> PartialOrd for Scc<'_, Ts> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<Ts: TransitionSystem> Ord for Scc<'_, Ts> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.first().cmp(&other.first())
    }
}
impl<Ts: TransitionSystem> std::hash::Hash for Scc<'_, Ts> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.states.hash(state);
    }
}

impl<'a, Ts: TransitionSystem> Scc<'a, Ts> {
    /// Creates a new strongly connected component from a transition system and a vector of state indices.
    pub fn new<I: IntoIterator<Item = Ts::StateIndex>>(ts: &'a Ts, indices: I) -> Self {
        let states: BTreeSet<_> = indices.into_iter().collect();
        assert!(!states.is_empty(), "Cannot have empty SCC!");
        let edges = OnceCell::new();
        let edge_colors = OnceCell::new();
        let minimal_representative = OnceCell::new();
        Self {
            ts,
            interior_transitions: edges,
            states,
            interior_edges: OnceCell::new(),
            border_edges: OnceCell::new(),
            border_transitions: OnceCell::new(),
            minimal_representative,
            edge_colors,
        }
    }

    /// Returns the `first` state of `self`. As we know that SCCs are always non-empty,
    /// this is guaranteed to return an element. It might, however, not always be the
    /// same between calls.
    pub fn first(&self) -> Ts::StateIndex {
        *self
            .states
            .first()
            .expect("SCC must contain at least one state")
    }

    /// Returns a reference to the underlying transition system.
    pub fn ts(&self) -> &'a Ts {
        self.ts
    }

    /// Returns an iterator over the state colors of the states in the SCC.
    pub fn state_colors(&self) -> impl Iterator<Item = Ts::StateColor> + '_ {
        self.iter().map(|q| {
            self.ts
                .state_color(*q)
                .expect("State is in SCC but not in Ts")
        })
    }

    /// Returns the size, i.e. the number of states in the SCC.
    pub fn size(&self) -> usize {
        assert!(!self.is_empty());
        self.states.len()
    }

    /// Returns `true` iff the SCC is trivial, meaning it consists of a single state.
    pub fn is_trivial(&self) -> bool {
        self.size() == 1
    }

    /// Gives a reference to all edges that leave the SCC, i.e. their source lies inside the
    /// SCC and the target lies outside of it.
    pub fn border_edges(&self) -> &BorderEdgeSet<Ts>
    where
        EdgeColor<Ts>: Hash + Eq,
    {
        self.border_edges.get_or_init(|| {
            let mut edges = Set::default();
            for q in &self.states {
                let it = self.ts.edges_from(*q).expect("State must exist");
                for edge in it {
                    let p = edge.target();
                    if !self.states.contains(&p) {
                        edges.insert((*q, edge.expression().clone(), edge.color().clone(), p));
                    }
                }
            }
            edges
        })
    }

    /// Gives a reference to all border edges of the SCC. A border edge is one whose
    /// source is in the SCC and whose target lies outside of the SCC.
    pub fn border_transitions(&self) -> &BorderTransitionSet<Ts>
    where
        EdgeColor<Ts>: Hash + Eq,
    {
        self.border_transitions.get_or_init(|| {
            let mut edges = Set::default();
            for q in &self.states {
                let it = self.ts.edges_from(*q).expect("State must exist");
                for edge in it {
                    let p = edge.target();
                    for a in edge.expression().symbols() {
                        if !self.states.contains(&p) {
                            edges.insert((*q, a, edge.color().clone(), p));
                        }
                    }
                }
            }
            edges
        })
    }

    /// Gives a reference to all interior edges of the SCC. An interior edge is an edge whose source
    /// and target states are in the SCC itself.
    ///
    /// This is computed lazily and cached.
    pub fn interior_edges(&self) -> &InteriorEdgeSet<Ts>
    where
        EdgeColor<Ts>: Hash + Eq,
    {
        self.interior_edges.get_or_init(|| {
            let mut edges = Set::default();
            for q in &self.states {
                let it = self.ts.edges_from(*q).expect("State must exist");
                for edge in it {
                    let p = edge.target();
                    if self.states.contains(&p) {
                        edges.insert((*q, edge.expression().clone(), edge.color().clone(), p));
                    }
                }
            }
            edges
        })
    }

    /// Gives a reference to all interior transitions of the SCC. An interior transitions is one whose source
    /// and target states are in the SCC itself.
    ///
    /// This is computed lazily and cached.
    pub fn interior_transitions(&self) -> &InteriorTransitionSet<Ts>
    where
        EdgeColor<Ts>: Hash + Eq,
    {
        self.interior_transitions.get_or_init(|| {
            let mut edges = Set::default();
            for q in &self.states {
                let it = self.ts.edges_from(*q).expect("State must exist");
                for edge in it {
                    let p = edge.target();
                    for a in edge.expression().symbols() {
                        if self.states.contains(&p) {
                            edges.insert((*q, a, edge.color().clone(), p));
                        }
                    }
                }
            }
            edges
        })
    }

    /// Computes the minimal word on which a state of this SCC may be reached.
    pub fn minimal_representative(&self) -> &Option<MinimalRepresentative<Ts>>
    where
        Ts: Pointed,
    {
        self.minimal_representative.get_or_init(|| {
            self.ts.minimal_representatives_iter().find_map(|rep| {
                if self.states.contains(&rep.state_index()) {
                    Some(rep)
                } else {
                    None
                }
            })
        })
    }

    /// Returns an iterator yielding the colors of edges whose source and target states are
    /// in the SCC.
    pub fn interior_edge_colors(&self) -> &Set<Ts::EdgeColor>
    where
        EdgeColor<Ts>: Hash + Eq,
    {
        self.edge_colors.get_or_init(|| {
            self.interior_transitions()
                .iter()
                .map(|(_, _, c, _)| c.clone())
                .collect()
        })
    }

    /// Returns a vector of the colors of the states in the SCC.
    pub fn colors(&self) -> Option<Vec<Ts::StateColor>> {
        debug_assert!(!self.is_empty());
        Some(
            self.states
                .iter()
                .filter_map(|q| self.ts.state_color(*q))
                .collect(),
        )
    }

    /// Attempts to compute a maximal word which is one that visits all states in the scc and uses
    /// each interior transition (one whose source and target are within the SCC) at least once.
    /// If no such word exists, `None` is returned.
    pub fn maximal_word(&self) -> Option<Vec<SymbolOf<Ts>>>
    where
        EdgeColor<Ts>: Hash + Eq,
    {
        self.maximal_loop_from(*self.states.first()?)
    }

    /// Attempts to compute a maximal word (i.e. a word visiting all states in the scc). If such a
    /// word exists, it is returned, otherwise the function returns `None`.
    /// This ensures that the word ends back in the state that it started from.
    pub fn maximal_loop_from(&self, from: Ts::StateIndex) -> Option<Vec<SymbolOf<Ts>>>
    where
        EdgeColor<Ts>: Hash + Eq,
    {
        assert!(self.contains(&from));
        let ts = self.ts;
        debug_assert!(!self.is_empty());

        let mut queue = math::OrderedMap::default();
        for (p, a, _, q) in self.interior_transitions() {
            queue
                .entry(*p)
                .or_insert_with(OrderedSet::default)
                .insert((*a, *q));
        }
        if queue.is_empty() {
            return None;
        }
        assert!(queue.contains_key(&from));

        let mut current = from;
        let mut word = Vec::new();

        while !queue.is_empty() {
            if queue.contains_key(&current) {
                if queue.get(&current).unwrap().is_empty() {
                    queue.remove(&current);
                    continue;
                } else {
                    let (symbol, target) = *queue
                        .get(&current)
                        .unwrap()
                        .iter()
                        .find_or_first(|(_, p)| *p == current)
                        .expect("We know this is non-empty");
                    debug_assert!(ts.has_transition(current, symbol, target));

                    queue.get_mut(&current).unwrap().remove(&(symbol, target));
                    word.push(symbol);
                    current = target;
                }
            } else {
                let q = self
                    .ts
                    .edges_from(current)
                    .and_then(|mut x| {
                        x.find_map(|e| {
                            if queue.contains_key(&e.target()) {
                                Some(e.target())
                            } else {
                                None
                            }
                        })
                    })
                    .unwrap_or_else(|| *queue.keys().next().unwrap());
                debug_assert!(queue.contains_key(&q));
                if queue.get(&q).unwrap().is_empty() {
                    queue.remove(&q);
                    continue;
                }

                word.extend(
                    ts.word_from_to(current, q)
                        .expect("Such a word must exist as both states are in the same SCC"),
                );
                current = q;
            }
        }

        if current != from {
            word.extend(
                ts.word_from_to(current, from)
                    .expect("they are in the same scc!"),
            );
        }

        Some(word)
    }

    /// Returns an iterator over the state indices making up the scc.
    pub fn state_indices(&self) -> std::collections::btree_set::Iter<'_, Ts::StateIndex> {
        self.states.iter()
    }

    /// Returns the number of states in the SCC.
    pub fn len(&self) -> usize {
        self.states.len()
    }

    /// Returns `true` if and only if the SCC is empty.
    pub fn is_empty(&self) -> bool {
        if self.len() == 0 {
            panic!("SCCs can never be empty!");
        }
        false
    }

    /// Returns `true` iff the SCC consists of a single state.
    pub fn is_singleton(&self) -> bool {
        self.states.len() == 1
    }

    /// Returns `true` iff the SCC is left on every symbol of the alphabet.
    pub fn is_transient(&self) -> bool
    where
        EdgeColor<Ts>: Hash + Eq,
    {
        self.interior_transitions().is_empty()
    }

    /// Returns `true` iff there is a transition from a state in the SCC to another state in the SCC,
    /// i.e. if there is a way of reading a non-empty word and staying in the SCC.
    pub fn is_nontransient(&self) -> bool
    where
        EdgeColor<Ts>: Hash + Eq,
    {
        !self.interior_transitions().is_empty()
    }
}

impl<Ts: TransitionSystem> Debug for Scc<'_, Ts> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            self.states.iter().map(|q| format!("{q:?}")).join(", ")
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::{TransitionSystem, DTS};
    use automata_core::math::Set;

    #[test]
    fn interior_transitions() {
        let transitions = [
            (0, 'a', 0, 0),
            (0, 'b', 1, 1),
            (1, 'a', 2, 1),
            (1, 'b', 0, 0),
        ]
        .into_iter()
        .collect::<Set<_>>();
        let ts = DTS::builder()
            .default_color(())
            .with_transitions(&transitions)
            .into_dts_with_initial(0);
        let sccs = ts.sccs();
        let first = sccs.first();

        assert_eq!(&transitions, first.interior_transitions());
        assert_eq!(first.interior_edge_colors(), &Set::from_iter([0, 1, 2]));

        let color_restricted = (&ts).edge_color_restricted(1, 2);
        let sccs = color_restricted.sccs();
        assert_eq!(sccs[0].interior_transitions(), &Set::default());
        assert_eq!(
            sccs[1].interior_transitions(),
            &Set::from_iter([(1, 'a', 2, 1)])
        );
    }
}
