use super::{Scc, SccDecomposition};
use crate::ts::{CompactIdMap, StateIndex};
use crate::{States, TransitionSystem};

/// Marker for an [`Sccs`] problem that considers all states of the transition system.
#[derive(Debug, Clone, Copy)]
pub struct AllStates;

/// The states from which an [`Sccs`] problem starts its search.
#[derive(Debug, Clone)]
pub struct Roots<I>(Vec<I>);

/// The problem of decomposing a transition system into strongly connected components, solved by
/// an iterative version of Tarjan's algorithm (so deep graphs do not overflow the stack).
///
/// ```
/// use automata::{DTS, ts::{Sccs, TransitionSystem}};
///
/// let ts = DTS::builder()
///     .default_color(())
///     .with_transitions([(0, 'a', (), 1), (1, 'a', (), 1), (1, 'b', (), 0)])
///     .into_dts_with_initial(0);
/// // all states (needs `States`)
/// assert_eq!(Sccs::on(&ts).compute().size(), 1);
/// // only the part that is reachable from the given states
/// assert_eq!(Sccs::on(&ts).from([1]).compute().size(), 1);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Sccs<'a, Ts, R = AllStates> {
    ts: &'a Ts,
    roots: R,
}

impl<'a, Ts: TransitionSystem> Sccs<'a, Ts> {
    /// Sets up the decomposition of `ts`. Without further configuration all of its states are
    /// considered, which requires [`States`].
    pub fn on(ts: &'a Ts) -> Self {
        Self {
            ts,
            roots: AllStates,
        }
    }

    /// Only decompose the part of the transition system that is reachable from the given states.
    /// States that do not exist are ignored.
    pub fn from<I>(self, roots: I) -> Sccs<'a, Ts, Roots<StateIndex<Ts>>>
    where
        I: IntoIterator<Item = StateIndex<Ts>>,
    {
        Sccs {
            ts: self.ts,
            roots: Roots(roots.into_iter().collect()),
        }
    }
}

impl<'a, Ts: States> Sccs<'a, Ts, AllStates> {
    /// Computes the decomposition of all states.
    pub fn compute(self) -> SccDecomposition<'a, Ts> {
        let roots: Vec<_> = self.ts.states().collect();
        // a dense numbering costs time proportional to the bound, which is not worth it if only
        // few of the states are considered (e.g. after removing states from a linked list system)
        let bound = self.ts.state_bound().filter(|&b| b <= 4 * roots.len());
        tarjan(self.ts, roots, bound)
    }
}

impl<'a, Ts: TransitionSystem> Sccs<'a, Ts, Roots<StateIndex<Ts>>> {
    /// Computes the decomposition of the states that are reachable from the roots.
    pub fn compute(self) -> SccDecomposition<'a, Ts> {
        tarjan(self.ts, self.roots.0, self.ts.state_bound())
    }
}

fn tarjan<Ts: TransitionSystem>(
    ts: &Ts,
    roots: Vec<StateIndex<Ts>>,
    bound: Option<usize>,
) -> SccDecomposition<'_, Ts> {
    const UNVISITED: usize = usize::MAX;

    // dense numbering of the states in order of discovery, so that all bookkeeping can use
    // plain vectors
    let mut ids = CompactIdMap::new(bound, roots.len());
    for &q in &roots {
        ids.get_or_insert(q);
    }
    let seeds = ids.len();

    let mut index = vec![UNVISITED; seeds];
    let mut low = vec![0usize; seeds];
    let mut on_stack = vec![false; seeds];
    let mut stack: Vec<usize> = Vec::new();
    let mut call_stack = Vec::new();
    let mut counter = 0usize;
    let mut sccs = Vec::new();

    for root in 0..seeds {
        if index[root] != UNVISITED {
            continue;
        }
        let Some(edges) = ts.edges_from(ids.state(root)) else {
            continue;
        };
        index[root] = counter;
        low[root] = counter;
        counter += 1;
        stack.push(root);
        on_stack[root] = true;
        call_stack.push((root, edges));

        while let Some((v, edges)) = call_stack.last_mut() {
            let v = *v;
            if let Some(edge) = edges.next() {
                let w = ids.get_or_insert(edge.target());
                if w == index.len() {
                    index.push(UNVISITED);
                    low.push(0);
                    on_stack.push(false);
                }
                if index[w] == UNVISITED {
                    index[w] = counter;
                    low[w] = counter;
                    counter += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    call_stack.push((
                        w,
                        ts.edges_from(ids.state(w))
                            .expect("the target of an edge exists"),
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
                    scc.push(ids.state(top));
                    if top == v {
                        break;
                    }
                }
                sccs.push(Scc::new(ts, scc));
            }
        }
    }

    sccs.sort();
    SccDecomposition::from_sccs(ts, sccs)
}

#[cfg(test)]
mod tests {
    use super::Sccs;
    use crate::Void;
    use crate::ts::Builder;

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

        let sccs = Sccs::on(&ts).compute();
        assert_eq!(sccs[0], vec![0]);
        assert_eq!(sccs[1], vec![1]);
        assert_eq!(sccs[2], vec![2, 3]);

        let sccs = Sccs::on(&ts).from([2]).compute();
        assert_eq!(sccs.size(), 1);
        assert_eq!(sccs[0], vec![2, 3]);
        assert_eq!(Sccs::on(&ts).from([0]).compute().size(), 3);
    }

    #[test]
    fn long_path_does_not_overflow_the_stack() {
        let n = 1_000_000;
        let ts = Builder::without_colors()
            .with_transitions((0..n - 1).map(|q| (q, 'a', Void, q + 1)))
            .into_right_congruence(0);
        assert_eq!(Sccs::on(&ts).from([0]).compute().size(), n as usize);
    }
}
