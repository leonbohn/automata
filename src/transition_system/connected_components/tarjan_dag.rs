use itertools::Itertools;
use std::hash::Hash;

use crate::prelude::*;
use dag::{Dag, ReachableIter};

use super::{EdgeColor, Scc, SccDecomposition};

/// Represents a hierarchical view on the SCCs of a transition system. It stores a reference ot the
/// original transition system and a [`Dag`] of SCCs. The SCCs are stored in topological order, i.e.,
/// the first SCC is the root of the DAG and all other SCCs are reachable from it.
#[derive(Clone)]
pub struct TarjanDAG<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    dag: Dag<Scc<'a, Ts>>,
}

impl<'a, Ts: TransitionSystem> TarjanDAG<'a, Ts> {}

impl<'a, Ts: TransitionSystem> From<SccDecomposition<'a, Ts>> for TarjanDAG<'a, Ts> {
    fn from(value: SccDecomposition<'a, Ts>) -> Self {
        let mut edges = Vec::new();
        for (l, ls) in value.1.iter().enumerate() {
            edges.extend(
                ls.iter()
                    .flat_map(|q| value.0.edges_from(*q).expect("We know this state exists!"))
                    .map(|o| (l, value.scc_of(o.target()).expect("Must be in some SCC")))
                    .unique(),
            );
        }
        Self {
            ts: value.0,
            dag: Dag::from_parts(value.1, edges),
        }
    }
}

impl<'a, Ts: TransitionSystem> std::fmt::Debug for TarjanDAG<'a, Ts> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.dag)
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::{transition_system::connected_components::tests::ts, TransitionSystem};

    #[test]
    fn tarjan_tree() {
        let cong = ts();
        let sccs = cong.sccs();
        let tree = super::TarjanDAG::from(sccs);
        assert_eq!(tree.size(), 3);
        assert_eq!(
            tree.reachable_from(0).sorted().collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
    }
}
