use crate::{math::Set, prelude::*};
use std::collections::VecDeque;

/// Type alias for a minimal representative of a state which is its length-lexicographically minimal
/// access sequence and its state index.
pub type MinimalRepresentative<Ts> = (Vec<SymbolOf<Ts>>, <Ts as TransitionSystem>::StateIndex);

/// Struct that can return the minimal representatives of a transition system. A minimal representative
/// for a state `q` of some transition system is the length-lexicographically minimal string with which
/// `q` can be reached from a given state.
#[derive(Debug, Clone)]
pub struct MinimalRepresentatives<Ts: TransitionSystem> {
    ts: Ts,
    seen: Set<Ts::StateIndex>,
    queue: VecDeque<MinimalRepresentative<Ts>>,
}

#[allow(missing_docs)]
impl<Ts> MinimalRepresentatives<Ts>
where
    Ts: TransitionSystem,
{
    pub fn new(ts: Ts, origin: Ts::StateIndex) -> Self {
        let seen = Set::from_iter([origin]);
        let queue = [(vec![], origin)].into_iter().collect();
        Self { ts, seen, queue }
    }
}

impl<Ts> Iterator for MinimalRepresentatives<Ts>
where
    Ts: TransitionSystem,
{
    type Item = MinimalRepresentative<Ts>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((access, q)) = self.queue.pop_front() {
            if let Some(it) = self.ts.edges_from(q) {
                for edge in it {
                    let p = edge.target();
                    if self.seen.insert(p) {
                        for sym in edge.expression().symbols() {
                            let mut new_access = access.clone();
                            new_access.push(sym);
                            self.queue.push_back((new_access, p))
                        }
                    }
                }
            }
            return Some((access, q));
        }
        None
    }
}

/// Allows iterating over the reachable states of a transition system.
#[derive(Debug, Clone)]
pub struct ReachableStates<Ts: TransitionSystem>(MinimalRepresentatives<Ts>);

#[allow(missing_docs)]
impl<Ts> ReachableStates<Ts>
where
    Ts: TransitionSystem,
{
    pub fn new(ts: Ts, origin: Ts::StateIndex) -> Self {
        Self(MinimalRepresentatives::new(ts, origin))
    }
}

impl<Ts> Iterator for ReachableStates<Ts>
where
    Ts: TransitionSystem,
{
    type Item = (Ts::StateIndex, StateColor<Ts>);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, q)| {
            (
                q,
                self.0.ts.state_color(q).expect(
                    "Something went wrong, every state should have a color but this one does not",
                ),
            )
        })
    }
}

/// Allows iterating over the indices of all reachable states in a [`TransitionSystem`].
#[derive(Debug, Clone)]
pub struct ReachableStateIndices<Ts: TransitionSystem>(MinimalRepresentatives<Ts>);

impl<Ts> Iterator for ReachableStateIndices<Ts>
where
    Ts: TransitionSystem,
{
    type Item = Ts::StateIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, q)| q)
    }
}

#[allow(missing_docs)]
impl<Ts> ReachableStateIndices<Ts>
where
    Ts: TransitionSystem,
{
    pub fn new(ts: Ts, origin: Ts::StateIndex) -> Self {
        Self(MinimalRepresentatives::new(ts, origin))
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::prelude::*;

    #[test]
    fn reachable_states() {
        let dfa = DFA::builder()
            .with_state_colors([false, false, true])
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 0),
                (1, 'a', 2),
                (1, 'b', 0),
                (2, 'a', 2),
                (2, 'b', 2),
            ])
            .into_dfa(0);

        assert_eq!(
            dfa.minimal_representatives_from(0).collect::<Vec<_>>(),
            vec![(vec![], 0), (vec!['a'], 1), (vec!['a', 'a'], 2)]
        );
        assert_eq!(dfa.reachable_state_indices().collect_vec(), vec![0, 1, 2]);
        assert_eq!(
            dfa.reachable_states().collect_vec(),
            vec![(0, false), (1, false), (2, true)]
        );

        assert_eq!(dfa.reachable_state_indices_from(2).collect_vec(), vec![2]);
    }
}
