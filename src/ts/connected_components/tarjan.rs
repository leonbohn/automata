use super::SccDecomposition;
use crate::TransitionSystem;
use crate::alphabet::Expression;
use crate::ts::connected_components::Scc;
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{CompactIdMap, IdType, IsEdge, StateIndex, StateMap};

#[derive(Debug, Clone)]
struct TarjanData {
    rootindex: Option<usize>,
}

/// Struct that is used to compute the strongly connected components of a transition system.
/// Many thanks go out to the authors of the petgraph crate <3.
#[derive(Debug, Clone)]
pub struct Tarjan<Idx> {
    index: usize,
    component_count: usize,
    stack: Vec<Idx>,
    data: StateMap<Idx, TarjanData>,
}

impl<Idx: IdType> Default for Tarjan<Idx> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Idx: IdType> Tarjan<Idx> {
    /// Creates a new Tarjan SCC decomposition instance.
    pub fn new() -> Self {
        Self {
            index: 0,
            component_count: usize::MAX,
            stack: Vec::new(),
            data: StateMap::default(),
        }
    }

    pub(crate) fn visit<Ts, F>(&mut self, ts: &Ts, v: Idx, f: &mut F)
    where
        Ts: TransitionSystem<StateIndex = Idx>,
        F: FnMut(&[Idx]),
    {
        let mut node_v_is_root = true;
        let node_v_index = self.index;
        self.data.insert(
            v,
            TarjanData {
                rootindex: Some(node_v_index),
            },
        );
        self.index += 1;

        if let Some(it) = ts.edges_from(v) {
            for edge in it {
                let q = edge.target();
                for _a in edge.expression().symbols() {
                    if self.data.get(&q).and_then(|data| data.rootindex).is_none() {
                        self.visit(ts, q, f);
                    }
                    let w_index = self.data.get(&q).unwrap().rootindex;
                    let v_mut = self.data.get_mut(&v).unwrap();
                    if w_index < v_mut.rootindex {
                        v_mut.rootindex = w_index;
                        node_v_is_root = false;
                    }
                }
            }
        }

        if node_v_is_root {
            let mut adjust = 1;
            let c = self.component_count;
            let node_data = &mut self.data;

            let start = self
                .stack
                .iter()
                .rposition(|w| {
                    if node_data.get(&v).unwrap().rootindex > node_data.get(w).unwrap().rootindex {
                        true
                    } else {
                        node_data.get_mut(w).unwrap().rootindex = Some(c);
                        adjust += 1;
                        false
                    }
                })
                .map(|x| x + 1)
                .unwrap_or_default();

            node_data.get_mut(&v).unwrap().rootindex = Some(c);
            self.stack.push(v);
            f(&self.stack[start..]);
            self.stack.truncate(start);
            self.index -= adjust;
            self.component_count -= 1;
        } else {
            self.stack.push(v);
        }
    }

    pub(crate) fn execute<Ts, F>(&mut self, ts: &Ts, mut f: F)
    where
        Ts: TransitionSystem<StateIndex = Idx>,
        F: FnMut(&[Idx]),
    {
        self.data = StateMap::new(ts.state_bound());

        for q in ts.state_indices() {
            if let Some(TarjanData { rootindex: None }) | None = self.data.get(&q) {
                self.visit(ts, q, &mut f);
            }
        }
        debug_assert!(self.stack.is_empty())
    }
}

/// Recursive application of Tarjan's algorithm form computing the SCC decomposition.
pub fn tarjan_scc_recursive<Ts>(ts: &Ts) -> SccDecomposition<'_, Ts>
where
    Ts: TransitionSystem,
{
    let mut sccs = Vec::new();
    {
        let mut tj = Tarjan::new();
        tj.execute(ts, |scc| sccs.push(Scc::new(ts, scc.to_vec())));
    }
    debug_assert!(
        sccs.iter().collect::<std::collections::HashSet<_>>().len() == sccs.len(),
        "All SCCs must be unique!"
    );
    sccs.sort();
    SccDecomposition::from_sccs(ts, sccs)
}

/// Implementation of Kosaraju's algorithm for computing the SCC decomposition.
/// Only states reachable from `start` are considered.
pub fn kosaraju<Ts>(ts: &Ts, start: Ts::StateIndex) -> SccDecomposition<'_, Ts>
where
    Ts: TransitionSystem + PredecessorIterable,
{
    // first pass: dfs on the forward graph, recording states in order of finishing
    let mut ids = CompactIdMap::new(ts.state_bound(), ts.hint_size().0);
    ids.get_or_insert(start);
    let mut finished = Vec::new();
    let mut queue = vec![(start, ts.edges_from(start).unwrap())];

    while let Some((q, edges)) = queue.last_mut() {
        let q = *q;
        if let Some(edge) = edges.next() {
            let target = edge.target();
            if ids.id(&target).is_none() {
                ids.get_or_insert(target);
                queue.push((target, ts.edges_from(target).unwrap()));
            }
        } else {
            queue.pop();
            finished.push(ids.id(&q).expect("state was numbered when discovered"));
        }
    }

    // second pass: backward dfs in decreasing order of finishing time, restricted to
    // states that have not been assigned to an scc yet
    let mut assigned = vec![false; ids.len()];
    let mut sccs = vec![];
    let mut work = vec![];

    for &root in finished.iter().rev() {
        if assigned[root] {
            continue;
        }
        assigned[root] = true;
        work.push(root);
        let mut scc = vec![];
        while let Some(v) = work.pop() {
            let q = ids.state(v);
            scc.push(q);
            for edge in ts.predecessors(q).into_iter().flatten() {
                if let Some(u) = ids.id(&edge.source())
                    && !assigned[u]
                {
                    assigned[u] = true;
                    work.push(u);
                }
            }
        }
        sccs.push(Scc::new(ts, scc));
    }

    SccDecomposition::from_sccs(ts, sccs)
}

/// Calls [`tarjan_scc_iterative_from`] for the set of all states.
pub fn tarjan_scc_iterative<Ts>(ts: &Ts) -> SccDecomposition<'_, Ts>
where
    Ts: TransitionSystem,
{
    tarjan_scc_iterative_from(ts, ts.state_indices())
}

/// Iterative application of Tarjan's algorithm form computing the SCC decomposition.
/// Only states reachable from `iter` through states contained in `iter` are considered.
pub fn tarjan_scc_iterative_from<Ts, I>(ts: &Ts, iter: I) -> SccDecomposition<'_, Ts>
where
    Ts: TransitionSystem,
    I: IntoIterator<Item = StateIndex<Ts>>,
{
    const UNVISITED: usize = usize::MAX;

    let start_time = std::time::Instant::now();
    let roots: Vec<_> = iter.into_iter().collect();

    // dense numbering of the considered states, so that all bookkeeping can use plain vectors
    // a dense numbering costs time proportional to the bound, which is not worth it if only few
    // of the states are considered (e.g. after removing states from a linked list system)
    let bound = ts.state_bound().filter(|&b| b <= 4 * roots.len());
    let mut ids = CompactIdMap::new(bound, roots.len());
    for &q in &roots {
        ids.get_or_insert(q);
    }
    let states = ids.states().to_vec();
    let n = states.len();

    let mut index = vec![UNVISITED; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut call_stack = Vec::new();
    let mut counter = 0usize;
    let mut sccs = Vec::new();

    for root in 0..n {
        if index[root] != UNVISITED {
            continue;
        }
        index[root] = counter;
        low[root] = counter;
        counter += 1;
        stack.push(root);
        on_stack[root] = true;
        call_stack.push((
            root,
            ts.edges_from(states[root])
                .expect("state is known to exist"),
        ));

        while let Some((v, edges)) = call_stack.last_mut() {
            let v = *v;
            if let Some(edge) = edges.next() {
                let Some(w) = ids.id(&edge.target()) else {
                    continue;
                };
                if index[w] == UNVISITED {
                    index[w] = counter;
                    low[w] = counter;
                    counter += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    call_stack.push((
                        w,
                        ts.edges_from(states[w]).expect("state is known to exist"),
                    ));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }

            call_stack.pop();
            if let Some(&(parent, _)) = call_stack.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == index[v] {
                let mut scc = vec![];
                loop {
                    let top = stack.pop().expect("root of scc is on the stack");
                    on_stack[top] = false;
                    scc.push(states[top]);
                    if top == v {
                        break;
                    }
                }
                sccs.push(Scc::new(ts, scc));
            }
        }
    }

    tracing::info!(
        "tarjan scc iterative took {}µs",
        start_time.elapsed().as_micros()
    );

    sccs.sort();
    SccDecomposition::from_sccs(ts, sccs)
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, time::Instant};

    use super::tarjan_scc_iterative;
    use crate::Pointed;
    use crate::Void;
    use crate::ts::{Builder, TransitionSystem};
    use crate::ts::{
        connected_components::{kosaraju, tarjan_scc_recursive},
        predecessors::PredecessorIterable,
    };
    use tracing::debug;

    #[test]
    fn kosaraju_agrees_with_tarjan() {
        // state 5 is not reachable from 0 but has an edge into the reachable part
        let ts = Builder::without_colors()
            .with_transitions([
                (0, 'a', Void, 1),
                (0, 'b', Void, 2),
                (1, 'a', Void, 0),
                (1, 'b', Void, 3),
                (2, 'a', Void, 2),
                (2, 'b', Void, 4),
                (3, 'a', Void, 4),
                (3, 'b', Void, 3),
                (4, 'a', Void, 2),
                (4, 'b', Void, 4),
                (5, 'a', Void, 0),
                (5, 'b', Void, 5),
            ])
            .into_right_congruence(0);

        let mut expected: Vec<Vec<_>> = tarjan_scc_iterative(&ts)
            .sccs_iter()
            .map(|scc| scc.iter().copied().collect())
            .filter(|scc: &Vec<_>| !scc.contains(&5))
            .collect();
        let mut actual: Vec<Vec<_>> = kosaraju(&ts, 0)
            .sccs_iter()
            .map(|scc| scc.iter().copied().collect())
            .collect();
        expected.sort();
        actual.sort();
        assert_eq!(actual, expected);
        assert_eq!(actual, vec![vec![0, 1], vec![2, 4], vec![3]]);
    }

    #[test]
    fn tarjan_iterative() {
        let ts = Builder::without_colors()
            .with_transitions([
                (0, 'a', Void, 0),
                (0, 'b', Void, 1),
                (0, 'c', Void, 2),
                (1, 'a', Void, 1),
                (2, 'a', Void, 3),
                (2, 'b', Void, 2),
                (3, 'a', Void, 2),
            ])
            .into_right_congruence(0);

        let rev = (&ts).reversed();
        let reachable = rev.reachable_state_indices_from(3).collect::<HashSet<_>>();

        assert!(reachable.contains(&3));
        assert!(reachable.contains(&2));

        let start = Instant::now();
        let _sccs = kosaraju(&ts, ts.initial());
        debug!("Kosaraju took {} microseconds", start.elapsed().as_micros());

        let start = Instant::now();
        let _sccs = tarjan_scc_recursive(&ts);
        debug!(
            "Tarjan recursive took {} microseconds",
            start.elapsed().as_micros()
        );

        let start = Instant::now();
        let sccs = tarjan_scc_iterative(&ts);
        debug!(
            "Tarjan iterative took {} microseconds",
            start.elapsed().as_micros()
        );
        assert_eq!(sccs[0], vec![0]);
        assert_eq!(sccs[1], vec![1]);
        assert_eq!(sccs[2], vec![2, 3]);
    }
}
