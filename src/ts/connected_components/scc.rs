use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::{cell::OnceCell, fmt::Debug};

use crate::alphabet::Expression;
use crate::congruence::MinimalRepresentative;
use crate::ts::{AccessWords, EdgeOf, StateIndex, SymbolOf};
use crate::{Pointed, TransitionSystem};
use itertools::Itertools;

/// Represents a strongly connected component of a transition system. It only stores its states;
/// edges are looked up in the transition system when asked for.
#[derive(Clone)]
pub struct Scc<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    /// sorted
    states: Vec<Ts::StateIndex>,
    access_words: Rc<OnceCell<AccessWords<'a, Ts>>>,
}

impl<Ts: TransitionSystem> IntoIterator for Scc<'_, Ts> {
    type IntoIter = std::vec::IntoIter<Ts::StateIndex>;
    type Item = Ts::StateIndex;
    fn into_iter(self) -> Self::IntoIter {
        self.states.into_iter()
    }
}

impl<Ts: TransitionSystem> std::ops::Deref for Scc<'_, Ts> {
    type Target = [Ts::StateIndex];

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
    /// Creates a new strongly connected component from a transition system and some state indices.
    pub fn new<I: IntoIterator<Item = Ts::StateIndex>>(ts: &'a Ts, indices: I) -> Self {
        let mut states: Vec<_> = indices.into_iter().collect();
        states.sort_unstable();
        states.dedup();
        assert!(!states.is_empty(), "Cannot have empty SCC!");
        Self {
            ts,
            states,
            access_words: Rc::new(OnceCell::new()),
        }
    }

    /// Makes `self` use the given cache of access words. [`SccDecomposition`](super::SccDecomposition)
    /// shares one cache between all of its SCCs so that a single search suffices for all of them.
    pub(super) fn share_access_words(&mut self, access_words: Rc<OnceCell<AccessWords<'a, Ts>>>) {
        self.access_words = access_words;
    }

    /// Returns the smallest state of `self`. As SCCs are never empty, this always exists.
    pub fn first(&self) -> Ts::StateIndex {
        self.states[0]
    }

    /// Returns a reference to the underlying transition system.
    pub fn ts(&self) -> &'a Ts {
        self.ts
    }

    /// Returns `true` iff `state` is part of the SCC.
    pub fn contains(&self, state: &Ts::StateIndex) -> bool {
        self.states.binary_search(state).is_ok()
    }

    /// Returns an iterator over the state colors of the states in the SCC.
    pub fn state_colors(&self) -> impl Iterator<Item = Ts::StateColor> + '_ {
        self.iter().map(|q| {
            self.ts
                .state_color(*q)
                .expect("State is in SCC but not in Ts")
                .into_owned()
        })
    }

    /// Returns the size, i.e. the number of states in the SCC.
    pub fn size(&self) -> usize {
        self.states.len()
    }

    /// Returns `true` iff the SCC is trivial, meaning it consists of a single state.
    pub fn is_trivial(&self) -> bool {
        self.size() == 1
    }

    /// All edges whose source lies inside the SCC, together with `true` if their target does, too.
    fn edges_with_inside(&self) -> impl Iterator<Item = (EdgeOf<'a, Ts>, bool)> + '_ {
        self.states.iter().flat_map(move |&q| {
            self.ts
                .edges_from(q)
                .expect("State is in SCC but not in Ts")
                .map(|edge| {
                    let inside = self.contains(&edge.target());
                    (edge, inside)
                })
        })
    }

    /// Returns the edges that leave the SCC, i.e. their source lies inside the SCC and the target
    /// lies outside of it.
    pub fn border_edges(&self) -> impl Iterator<Item = EdgeOf<'a, Ts>> + '_ {
        self.edges_with_inside()
            .filter_map(|(edge, inside)| (!inside).then_some(edge))
    }

    /// Returns the edges whose source and target both lie in the SCC.
    pub fn interior_edges(&self) -> impl Iterator<Item = EdgeOf<'a, Ts>> + '_ {
        self.edges_with_inside()
            .filter_map(|(edge, inside)| inside.then_some(edge))
    }

    /// Computes the minimal word on which a state of this SCC may be reached, if any state of the
    /// SCC is reachable from the initial state.
    pub fn minimal_representative(&self) -> Option<MinimalRepresentative<Ts>>
    where
        Ts: Pointed,
    {
        let access = self.access_words.get_or_init(|| {
            let mut access = AccessWords::new(self.ts, self.ts.initial());
            access.complete();
            access
        });
        let state = self
            .states
            .iter()
            .filter_map(|&q| access.rank(q).map(|rank| (rank, q)))
            .min()?
            .1;
        Some(MinimalRepresentative::new(access.word(state)?, state))
    }

    /// Returns an iterator yielding the colors of edges whose source and target states are
    /// in the SCC. A color appears once per edge that carries it.
    pub fn interior_edge_colors(&self) -> impl Iterator<Item = Ts::EdgeColor> + '_ {
        self.interior_edges().map(|edge| edge.color().clone())
    }

    /// Returns a vector of the colors of the states in the SCC.
    pub fn colors(&self) -> Option<Vec<Ts::StateColor>> {
        Some(
            self.states
                .iter()
                .filter_map(|q| self.ts.state_color(*q).map(Cow::into_owned))
                .collect(),
        )
    }

    /// Attempts to compute a maximal word which is one that visits all states in the scc and uses
    /// each interior transition (one whose source and target are within the SCC) at least once.
    /// If no such word exists, `None` is returned.
    pub fn maximal_word(&self) -> Option<Vec<SymbolOf<Ts>>> {
        self.maximal_loop_from(self.first())
    }

    /// Attempts to compute a maximal word (i.e. a word visiting all states in the scc). If such a
    /// word exists, it is returned, otherwise the function returns `None`.
    /// This ensures that the word ends back in the state that it started from.
    pub fn maximal_loop_from(&self, from: Ts::StateIndex) -> Option<Vec<SymbolOf<Ts>>> {
        assert!(self.contains(&from));
        let ts = self.ts;

        let mut queue = BTreeMap::default();
        for edge in self.interior_edges() {
            for a in edge.expression().symbols() {
                queue
                    .entry(edge.source())
                    .or_insert_with(BTreeSet::default)
                    .insert((a, edge.target()));
            }
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
    pub fn state_indices(&self) -> std::slice::Iter<'_, Ts::StateIndex> {
        self.states.iter()
    }

    /// Returns `true` iff the SCC consists of a single state.
    pub fn is_singleton(&self) -> bool {
        self.is_trivial()
    }

    /// Returns `true` iff the SCC is left on every symbol of the alphabet.
    pub fn is_transient(&self) -> bool {
        self.interior_edges().next().is_none()
    }

    /// Returns `true` iff there is a transition from a state in the SCC to another state in the SCC,
    /// i.e. if there is a way of reading a non-empty word and staying in the SCC.
    pub fn is_nontransient(&self) -> bool {
        !self.is_transient()
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
    use crate::alphabet::Expression;
    use crate::ts::Sccs;
    use crate::{DTS, TransitionSystem};

    #[test]
    fn interior_edges() {
        let transitions = [
            (0, 'a', 0, 0),
            (0, 'b', 1, 1),
            (1, 'a', 2, 1),
            (1, 'b', 0, 0),
        ];
        let ts = DTS::builder()
            .default_color(())
            .with_transitions(transitions)
            .into_dts_with_initial(0);
        let sccs = Sccs::on(&ts).compute();
        let first = sccs.first();

        let mut interior: Vec<_> = first
            .interior_edges()
            .flat_map(|e| {
                e.expression()
                    .symbols()
                    .map(|a| (e.source(), a, *e.color(), e.target()))
                    .collect::<Vec<_>>()
            })
            .collect();
        interior.sort();
        assert_eq!(interior, transitions);
        assert_eq!(first.border_edges().count(), 0);
        let mut colors: Vec<_> = first.interior_edge_colors().collect();
        colors.sort();
        assert_eq!(colors, [0, 0, 1, 2]);

        let color_restricted = (&ts).edge_color_restricted(1, 2);
        let sccs = Sccs::on(&color_restricted).compute();
        assert_eq!(sccs[0].interior_edges().count(), 0);
        assert_eq!(sccs[0].border_edges().count(), 1);
        assert_eq!(sccs[1].interior_edge_colors().collect::<Vec<_>>(), [2]);
    }
}
