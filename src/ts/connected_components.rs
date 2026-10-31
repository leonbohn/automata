use crate::ts::EdgeOf;
use crate::ts::States;
use rustc_hash::FxHashMap;
use std::hash::Hash;

use crate::dag::Dag;
use crate::math;
use itertools::Itertools;
use tracing::trace;

mod scc;
pub use scc::Scc;

mod tarjan;
use crate::TransitionSystem;
pub use tarjan::{AllStates, Roots, Sccs};

/// Newtype wrapper for storing indices of SCCs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SccIndex(usize);

impl std::fmt::Display for SccIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SCC{}", self.0)
    }
}

impl std::ops::Deref for SccIndex {
    type Target = usize;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for SccIndex {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Represents a decomposition of a transition system into strongly connected components.
#[derive(Clone)]
pub struct SccDecomposition<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    dag: Dag<Scc<'a, Ts>>,
    index_of: FxHashMap<Ts::StateIndex, usize>,
}

impl<'a, Ts: TransitionSystem> std::ops::Deref for SccDecomposition<'a, Ts> {
    type Target = Dag<Scc<'a, Ts>>;

    fn deref(&self) -> &Self::Target {
        &self.dag
    }
}

impl<'a, Ts: TransitionSystem> SccDecomposition<'a, Ts> {
    /// Creates a new SCC decomposition from a transition system and a vector of SCCs.
    pub fn from_sccs(ts: &'a Ts, mut sccs: Vec<Scc<'a, Ts>>) -> Self {
        let access_words = std::rc::Rc::new(std::cell::OnceCell::new());
        for scc in &mut sccs {
            scc.share_access_words(access_words.clone());
        }
        let mut index_of = FxHashMap::default();
        for (i, scc) in sccs.iter().enumerate() {
            index_of.extend(scc.iter().map(|q| (*q, i)));
        }
        let mut edges = Vec::new();
        let mut targets = math::FxIndexSet::default();
        for (i, source) in sccs.iter().enumerate() {
            trace!(
                "Processing SCC {i} with states {}",
                source.iter().map(|q| format!("{q:?}")).join(", ")
            );
            targets.clear();
            for q in source.iter() {
                let Some(it) = ts.successor_indices(*q) else {
                    continue;
                };
                for target in it {
                    // a decomposition of only some of the states has edges that leave it
                    let Some(&target_scc_index) = index_of.get(&target) else {
                        continue;
                    };
                    // no self loops and check that no such edge is present, already
                    if target_scc_index == i || !targets.insert(target_scc_index) {
                        continue;
                    }
                    edges.push((i, target_scc_index));
                }
            }
        }
        Self {
            ts,
            dag: Dag::from_parts(sccs, edges),
            index_of,
        }
    }

    /// Returns an iterator over all transient edges in the transition system. An edge is transient
    /// if its source and target are in different SCCs.
    pub fn transient_edges(&self) -> impl Iterator<Item = EdgeOf<'a, Ts>> + '_
    where
        Ts: States,
    {
        self.ts.transitions().filter(move |t| {
            let source = t.source();
            let target = t.target();
            self.scc_index_of(source) != self.scc_index_of(target)
        })
    }

    /// Returns an iterator over all transient states in the transition system. A state is transient
    /// if it is in a singleton SCC and there are no self loops. This means that from the state, there
    /// is no way to reach itself.
    pub fn transient_states(&self) -> impl Iterator<Item = Ts::StateIndex> + '_ {
        self.dag
            .nodes()
            .filter_map(|scc| {
                if scc.is_transient() {
                    Some(scc.iter().cloned())
                } else {
                    None
                }
            })
            .flatten()
    }

    /// Returns the index of the SCC containing the given state, if it exists.
    pub fn scc_index_of(&self, state: Ts::StateIndex) -> Option<SccIndex> {
        self.index_of.get(&state).copied().map(SccIndex)
    }

    /// Returns an iterator over sccs which are reachable from the given source scc.
    pub fn reachable_from(&self, source: SccIndex) -> crate::dag::ReachableIter<'_, Scc<'a, Ts>> {
        self.dag.reachable_from(source.0)
    }

    /// Returns the number of SCCs in the transition system which is equal to the size
    /// of the DAG.
    pub fn size(&self) -> usize {
        self.dag.size()
    }

    /// Returns the number of SCCs which are not transient, meaning an SCC counts towards
    /// the total if there is at least one transition that starts and ends in it.
    pub fn proper_size(&self) -> usize {
        self.dag
            .iter()
            .filter(|(_, scc)| scc.is_nontransient())
            .count()
    }

    /// Returns the SCC containing the given state, if it exists.
    pub fn scc_of(&self, state: Ts::StateIndex) -> Option<&Scc<'a, Ts>> {
        self.scc_index_of(state).map(|i| &self.dag[i.0])
    }

    /// Returns the SCC with the given index.
    pub fn scc(&self, index: SccIndex) -> &Scc<'a, Ts> {
        &self.dag[index.0]
    }

    /// Returns an iterator over all SCCs in the transition system.
    pub fn sccs_iter(&self) -> impl Iterator<Item = &Scc<'a, Ts>> + '_ {
        self.dag.nodes()
    }

    /// Folds the state colors of the SCCs of the transition system into a single value.
    pub fn fold_state_colors<F, D>(&self, init: D, f: F) -> Dag<D>
    where
        D: Clone,
        F: FnMut(D, Ts::StateColor) -> D + Copy,
    {
        self.dag.reduce(|x| x.state_colors().fold(init.clone(), f))
    }

    /// Folds the colors of all edges whose source and target are in the same SCC into
    /// a single value.
    pub fn fold_edge_colors<F, D>(&self, init: D, f: F) -> Dag<D>
    where
        D: Clone,
        F: FnMut(D, Ts::EdgeColor) -> D + Copy,
    {
        self.dag
            .reduce(|x| x.interior_edge_colors().fold(init.clone(), f))
    }

    /// Gives a reference to the actual DAG produced by the decomposition.
    pub fn dag(&self) -> &Dag<Scc<'a, Ts>> {
        &self.dag
    }

    /// Returns an iterator over all SCCs which are terminal, meaning they have no outgoing
    /// edges to another SCC.
    pub fn terminal_sccs(&self) -> impl Iterator<Item = &Scc<'a, Ts>> {
        self.dag
            .iter()
            .filter_map(|(_, scc)| scc.border_edges().next().is_none().then_some(scc))
    }

    /// Gives the first [`Scc`] in the decomposition. This must exist as we only allow
    /// non-empty decompositions.
    ///
    /// # Panics
    /// Panics if the decomposition is empty, which cannot happen for a decomposition computed by
    /// this crate.
    pub fn first(&self) -> &Scc<'a, Ts> {
        assert!(!self.dag.is_empty(), "At least one SCC must exist!");
        &self.dag[0]
    }

    /// Tries to find a nontrivial SCC and if it finds one, asserts that it is the only one.
    ///
    /// # Panics
    /// Panics if there is more than one nontrivial SCC.
    pub fn singleton_nontrivial(&self) -> Option<&Scc<'a, Ts>> {
        for i in 0..self.dag.size() {
            if self.dag[i].is_trivial() || self.dag[i].is_transient() {
                continue;
            }

            for j in (i + 1)..self.dag.size() {
                assert!(self.dag[j].is_transient() || self.dag[j].is_trivial())
            }

            return Some(&self.dag[i]);
        }
        None
    }

    /// Tests whether two SCC decompositions are isomorphic. This is done by checking whether each
    /// SCC in one decomposition has a matching SCC in the other decomposition.
    pub fn equivalent(&self, other: &SccDecomposition<'a, Ts>) -> bool {
        for elem in self.dag.iter() {
            if !other.dag.iter().any(|other_elem| elem == other_elem) {
                trace!("found no scc matching {elem:?} in other");
                return false;
            }
        }
        for scc in other.dag.iter() {
            if !self.dag.iter().any(|other_scc| scc == other_scc) {
                trace!("found no scc matching {scc:?} in self");
                return false;
            }
        }
        true
    }
}

impl<Ts: TransitionSystem> std::fmt::Debug for SccDecomposition<'_, Ts> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{{{}}}",
            self.dag
                .iter()
                .map(|(_, scc)| format!("[{}]", scc.iter().map(|q| format!("{q:?}")).join(", ")))
                .join(", "),
        )
    }
}

impl<Ts: TransitionSystem> Hash for SccDecomposition<'_, Ts> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.dag.hash(state)
    }
}

impl<Ts: TransitionSystem> PartialEq for SccDecomposition<'_, Ts> {
    fn eq(&self, other: &Self) -> bool {
        self.dag == other.dag
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn decomposition_from_roots_covers_the_reachable_part() {
        let ts = ts();
        let sccs = Sccs::on(&ts).from([0]).compute();
        assert_eq!(sccs.size(), 3);
        assert_eq!(sccs.scc_of(0).unwrap().size(), 1);
        let sccs = Sccs::on(&ts).from([2, 3]).compute();
        assert_eq!(sccs.size(), 1);
        assert_eq!(sccs.scc_of(3).unwrap().size(), 2);
    }
    use crate::ts::Sccs;

    use crate::ts::Builder;
    use crate::{
        RightCongruence,
        ts::connected_components::{Scc, SccDecomposition},
    };

    pub(super) fn ts() -> RightCongruence {
        Builder::without_colors()
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 2),
                (1, 'a', 1),
                (1, 'b', 1),
                (2, 'a', 3),
                (2, 'b', 2),
                (3, 'a', 3),
                (3, 'b', 2),
            ])
            .into_right_congruence(0)
    }

    #[test]
    fn tarjan_scc_decomposition() {
        let cong = ts();
        let sccs = Sccs::on(&cong).compute();

        let scc1 = Scc::new(&cong, vec![0]);
        let scc2 = Scc::new(&cong, vec![1]);
        let scc3 = Scc::new(&cong, vec![2, 3]);

        assert_eq!(
            sccs,
            SccDecomposition::from_sccs(&cong, vec![scc1.clone(), scc2.clone(), scc3.clone()])
        );

        assert_eq!(scc2.interior_edges().count(), 2);
        assert_eq!(scc3.interior_edges().count(), 4);
        assert_eq!(scc3.border_edges().count(), 0);
        assert_eq!(scc1.border_edges().count(), 2);

        assert_eq!(scc1.maximal_word(), None);
        assert_eq!(scc2.maximal_word(), Some(vec!['a', 'b']));
        assert_eq!(scc3.maximal_word(), Some(vec!['b', 'a', 'a', 'b']))
    }
}
