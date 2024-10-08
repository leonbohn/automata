use std::hash::Hash;

use itertools::Itertools;
use tracing::trace;

use crate::prelude::*;

mod scc;
pub use scc::Scc;

mod tarjan;
pub use tarjan::{kosaraju, tarjan_scc_iterative, tarjan_scc_iterative_from, tarjan_scc_recursive};

mod tarjan_dag;
pub use tarjan_dag::TarjanDAG;

/// Represents a decomposition of a transition system into strongly connected components.
#[derive(Clone)]
pub struct SccDecomposition<'a, Ts: TransitionSystem>(&'a Ts, Vec<Scc<'a, Ts>>);

impl<'a, Ts: TransitionSystem> std::ops::Deref for SccDecomposition<'a, Ts> {
    type Target = Vec<Scc<'a, Ts>>;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

impl<'a, Ts: TransitionSystem> SccDecomposition<'a, Ts> {
    /// Creates a new SCC decomposition from a transition system and a vector of SCCs.
    pub fn new(ts: &'a Ts, sccs: Vec<Scc<'a, Ts>>) -> Self {
        Self(ts, sccs)
    }

    /// Gives the first [`Scc`] in the decomposition. This must exist as we only allow
    /// non-empty decompositions.
    pub fn first(&self) -> &Scc<'a, Ts> {
        self.1.first().expect("At least one SCC must exist!")
    }

    /// Tries to find a nontrivial SCC and if it finds one, asserts that it is the only one.
    pub fn singleton_nontrivial(&self) -> Option<&Scc<'a, Ts>> {
        for i in 0..self.1.len() {
            if self.1[i].is_trivial() || self.1[i].is_transient() {
                continue;
            }

            for j in (i + 1)..self.1.len() {
                assert!(self.1[j].is_transient() || self.1[j].is_trivial())
            }

            return Some(&self.1[i]);
        }
        None
    }

    /// Attepmts to find the index of a the SCC containing the given `state`. Returns this index if
    /// it exists, otherwise returns `None`.
    pub fn scc_of(&self, state: Ts::StateIndex) -> Option<usize> {
        self.1
            .iter()
            .enumerate()
            .find_map(|(i, scc)| if scc.contains(&state) { Some(i) } else { None })
    }

    /// Tests whether two SCC decompositions are isomorphic. This is done by checking whether each
    /// SCC in one decomposition has a matching SCC in the other decomposition.
    pub fn isomorphic(&self, other: &SccDecomposition<'a, Ts>) -> bool {
        for scc in &self.1 {
            if !other.1.iter().any(|other_scc| scc == other_scc) {
                trace!("found no scc matching {scc:?} in other");
                return false;
            }
        }
        for scc in &other.1 {
            if !self.1.iter().any(|other_scc| scc == other_scc) {
                trace!("found no scc matching {scc:?} in self");
                return false;
            }
        }
        true
    }
}

impl<'a, Ts: TransitionSystem> std::fmt::Debug for SccDecomposition<'a, Ts> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{{{}}}",
            self.1
                .iter()
                .map(|scc| format!("[{}]", scc.iter().map(|q| format!("{q:?}")).join(", ")))
                .join(", "),
        )
    }
}

impl<'a, Ts: TransitionSystem> Hash for SccDecomposition<'a, Ts> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.1.hash(state)
    }
}

impl<'a, Ts: TransitionSystem> PartialEq for SccDecomposition<'a, Ts> {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}

#[cfg(test)]
mod tests {
    use math::Set;

    use crate::{
        prelude::*,
        transition_system::connected_components::{Scc, SccDecomposition},
    };

    pub(super) fn ts() -> RightCongruence<CharAlphabet> {
        TSBuilder::without_colors()
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
        let sccs = cong.sccs();

        let scc1 = Scc::new(&cong, vec![0]);
        let scc2 = Scc::new(&cong, vec![1]);
        let scc3 = Scc::new(&cong, vec![2, 3]);

        assert_eq!(
            sccs,
            SccDecomposition::new(&cong, vec![scc1.clone(), scc2.clone(), scc3.clone()])
        );

        assert_eq!(
            scc2.interior_transitions(),
            &Set::from_iter([(1, 'a', Void, 1), (1, 'b', Void, 1)])
        );
        assert_eq!(
            scc3.interior_transitions(),
            &Set::from_iter([
                (2, 'a', Void, 3),
                (2, 'b', Void, 2),
                (3, 'a', Void, 3),
                (3, 'b', Void, 2)
            ])
        );

        assert_eq!(scc1.maximal_word(), None);
        assert_eq!(scc2.maximal_word(), Some(vec!['a', 'b']));
        assert_eq!(scc3.maximal_word(), Some(vec!['b', 'a', 'a', 'b']))
    }
}
