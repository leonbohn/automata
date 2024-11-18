use std::{collections::BTreeSet, hash::Hash};

use automata_core::{alphabet::SimpleAlphabet, Color, Int};
use itertools::Itertools;
use tracing::trace;

use crate::{
    automaton::{MaxEvenParityCondition, DPA, NBA},
    ts::{DefaultIdType, ForAlphabet, IndexType, IsEdge, Sproutable, SymbolOf},
    TransitionSystem, DTS,
};

/// Represents a macrostate that is used for the determinization of a Büchi automaton.
#[derive(Clone)]
pub struct Macrostate<Idx = DefaultIdType> {
    states: Vec<BTreeSet<Idx>>,
    ranks: Vec<usize>,
}

impl std::fmt::Debug for Macrostate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        assert_eq!(self.states.len(), self.ranks.len());
        write!(
            f,
            "[{}]",
            self.states
                .iter()
                .zip(&self.ranks)
                .map(|(states, rank)| format!(
                    "{rank}:{{{}}}",
                    states.iter().map(|i| i.to_string()).join(", ")
                ))
                .join(", ")
        )
    }
}

impl<Idx: Eq> PartialEq for Macrostate<Idx> {
    fn eq(&self, other: &Self) -> bool {
        self.states == other.states && self.ranks == other.ranks
    }
}
impl<Idx: Eq> Eq for Macrostate<Idx> {}
impl<Idx: Hash> Hash for Macrostate<Idx> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.states.hash(state);
        self.ranks.hash(state);
    }
}

impl<Idx: IndexType> Macrostate<Idx> {
    fn _sanity_checked(self) -> Self {
        if !cfg!(debug_assertions) {
            tracing::warn!("Macrostate::_sanity_check called without debug_assertions");
            return self;
        }
        assert_eq!(self.states.len(), self.ranks.len());
        for (i, state) in self.states.iter().enumerate() {
            for (j, other) in self.states.iter().enumerate() {
                if i != j {
                    if !state.is_disjoint(other) {
                        tracing::error!(
                            "states[{}]={:?} and states[{}]={:?} are not disjoint",
                            i,
                            state,
                            j,
                            other
                        );
                    }
                }
            }
        }
        for (i, rank) in self.ranks.iter().enumerate() {
            for (j, other) in self.ranks.iter().enumerate() {
                if i != j {
                    if rank == other {
                        tracing::error!(
                            "ranks[{}]={:?} and ranks[{}]={:?} are equal",
                            i,
                            rank,
                            j,
                            other
                        );
                    }
                }
            }
        }
        self
    }
    /// Returns a set of all state indices that occur in this macrostate.
    pub fn flat_partition(&self) -> BTreeSet<Idx> {
        self.states.iter().flatten().cloned().collect()
    }
    /// Gives a reference to the partition of the macrostate.
    pub fn partition(&self) -> &[BTreeSet<Idx>] {
        &self.states
    }
    /// Gives a reference to the ranks.
    pub fn ranks(&self) -> &[usize] {
        &self.ranks
    }
    fn from_parts(states: Vec<BTreeSet<Idx>>, ranks: Vec<usize>) -> Self {
        Macrostate { states, ranks }._sanity_checked()
    }
    fn into_parts(self) -> (Vec<BTreeSet<Idx>>, Vec<usize>) {
        (self.states, self.ranks)
    }
    fn compute_successor<T: TransitionSystem<StateIndex = Idx, StateColor = bool>>(
        &self,
        ts: T,
        sym: SymbolOf<T>,
    ) -> (Self, Int) {
        debug_assert_eq!(self.states.len(), self.ranks.len());
        if self.states.is_empty() {
            // we are in a sink state
            return (Self::from_parts(vec![], vec![]), 0);
        }

        let print_states = |states: &[BTreeSet<Idx>]| {
            states
                .iter()
                .map(|s| format!("{{{}}}", s.iter().map(|i| format!("{:?}", i)).join(", ")))
                .join(", ")
        };
        let print_ranking = |ranks: &[usize]| ranks.iter().map(|r| r.to_string()).join(", ");
        let print_partial_ranking = |ranks: &[Option<usize>]| {
            ranks
                .iter()
                .map(|r| match r {
                    Some(rank) => rank.to_string(),
                    None => "#".to_string(),
                })
                .join(", ")
        };

        let mut states_out = Vec::with_capacity(2 * self.states.len());
        let mut ranking_out = vec![];

        // split successors into final and non-final
        for i in 0..self.states.len() {
            let mut accepting = BTreeSet::new();
            let mut nonaccepting = BTreeSet::new();
            for state in &self.states[i] {
                for edge in ts.edges_matching(*state, sym).unwrap() {
                    let target = edge.target();
                    if ts.state_color(target).unwrap() {
                        accepting.insert(target);
                    } else {
                        nonaccepting.insert(target);
                    }
                }
            }
            states_out.extend([accepting, nonaccepting]);
            ranking_out.extend([None, Some(self.ranks[i])]);
        }

        trace!(
            "split {} {} for symbol {sym:?}\t{}\t{}",
            print_states(&self.states),
            print_ranking(&self.ranks),
            print_states(&states_out),
            print_partial_ranking(&ranking_out),
        );

        // remove duplicates
        assert!(!states_out.is_empty());
        assert!(states_out.len() == ranking_out.len());

        let mut seen = BTreeSet::from_iter(states_out[0].iter().cloned());
        for i in 1..states_out.len() {
            states_out[i].retain(|s| seen.insert(*s));
        }

        trace!("dedup to {}", print_states(&states_out));

        // move ranks to the left
        let mut disappeared = vec![];
        let mut survived = vec![];
        'outer: for i in 0..ranking_out.len() {
            let Some(rank) = ranking_out[i] else {
                continue 'outer;
            };
            if !states_out[i].is_empty() {
                // the rank stays
                continue 'outer;
            }
            // we need to move the rank to the left
            ranking_out[i] = None;
            'inner: for j in (0..i).rev() {
                if states_out[j].is_empty() {
                    assert!(ranking_out[j].is_none());
                    continue 'inner;
                }
                // we found a non-empty set
                if let Some(old_rank) = ranking_out[j] {
                    if old_rank < rank {
                        disappeared.push(old_rank);
                        survived.push(rank);
                        ranking_out[j] = Some(rank);
                    } else {
                        disappeared.push(rank);
                    }
                    continue 'outer;
                } else {
                    ranking_out[j] = Some(rank);
                    survived.push(rank);
                    continue 'outer;
                }
            }
            // did not find a non-empty set
            disappeared.push(rank);
        }
        trace!(
            "moved ranks: {}, S: {{{}}}, D: {{{}}}",
            print_partial_ranking(&ranking_out),
            survived.iter().join(", "),
            disappeared.iter().join(", ")
        );

        // remove empty sets
        let mut states = vec![];
        let mut ranks = vec![];
        for (i, state) in states_out.into_iter().enumerate() {
            if !state.is_empty() {
                states.push(state);
                ranks.push(ranking_out[i]);
            }
        }

        if states.is_empty() {
            // we have no states left
            ranks.clear();
            return (Self::from_parts(vec![], vec![]), 0);
        }
        trace!(
            "without empty: {} {}",
            print_states(&states),
            print_partial_ranking(&ranks)
        );

        // normalize ranks
        // first close gaps
        for i in 0..ranks.len() {
            let Some(rank) = ranks[i] else {
                continue;
            };
            let next_higher_rank = ranks
                .iter()
                .filter_map(|r| if r.unwrap_or(0) > rank { *r } else { None })
                .min()
                .unwrap_or(rank);
            if rank + 1 < next_higher_rank {
                ranks[i] = Some(next_higher_rank - 1);
            }
        }
        trace!("no gaps: {}", print_partial_ranking(&ranks));

        // then add ranks for missing
        let mut completed = vec![];
        let mut least = ranks.iter().filter_map(|r| *r).min().unwrap();
        for i in 0..states.len() {
            if let Some(rank) = ranks[i] {
                completed.push(rank);
            } else {
                least -= 1;
                completed.push(least);
            }
        }
        trace!("no missing: {}", print_ranking(&completed));

        // compute transition priority
        let priority = if let Some(max_active) = survived.iter().chain(disappeared.iter()).max() {
            if survived.contains(&max_active) {
                trace!("max active {max_active} so priority {}", 2 * max_active);
                2 * max_active
            } else {
                trace!("max active {max_active} so priority {}", 2 * max_active + 1);
                2 * max_active + 1
            }
        } else {
            trace!("no active ranks so priority 1");
            1
        };

        (
            Self::from_parts(states, completed)._sanity_checked(),
            priority as Int,
        )
    }
}

/// Performs a determinization of the given `NBA` to a `DPA`.
pub fn nbadet<A: SimpleAlphabet, Q: Color>(
    nba: NBA<A, Q>,
) -> DPA<A, Macrostate, MaxEvenParityCondition> {
    let start_time = std::time::Instant::now();

    let initial =
        Macrostate::from_parts(vec![nba.initial_states_iter().collect()], vec![nba.size()]);
    let universe = nba.alphabet().universe().collect_vec();

    let mut states = vec![initial.clone()];
    let mut current = 0;
    let mut ts: DTS<A, Macrostate, Int> = DTS::for_alphabet(nba.alphabet().clone());
    ts.add_state(initial);

    while current < states.len() {
        for sym in &universe {
            let (succ, prio) = states[current].compute_successor(&nba, *sym);
            if let Some(pos) = states.iter().position(|s| s == &succ) {
                trace!(
                    "macrostate {:?} at position [{}], adding transition {:?} --{:?}--> {:?}",
                    states[pos],
                    pos,
                    current,
                    sym,
                    pos
                );
                ts.add_edge((current as DefaultIdType, *sym, prio, pos as DefaultIdType));
            } else {
                trace!(
                    "new macrostate {:?} and edge {:?} --{:?}--> {:?}",
                    succ,
                    current,
                    sym,
                    states.len()
                );
                let pos = states.len();
                states.push(succ.clone());
                let state_id = ts.add_state(succ);
                assert_eq!(state_id, pos as DefaultIdType);
                ts.add_edge((current as DefaultIdType, *sym, prio, pos as DefaultIdType));
            }
        }
        current += 1;
    }

    tracing::info!(
        "determinized NBA of size {} to DPA with {} states transitions in {}",
        nba.size(),
        ts.size(),
        automata_core::show_duration(start_time.elapsed())
    );
    DPA::from_parts(ts, 0)
}

#[cfg(test)]
mod tests {
    use automata_core::upw;

    use crate::{dot::Dottable, ts::TSBuilder, TransitionSystem};

    #[test_log::test]
    fn nbadet() {
        let nba_fin_b = TSBuilder::without_edge_colors()
            .with_state_colors([false, true])
            .with_edges([
                (0, 'a', 0),
                (0, 'b', 0),
                (0, 'a', 1),
                (0, 'b', 1),
                (1, 'a', 1),
            ])
            .into_nba([0]);

        let dpa_fin_b = super::nbadet(nba_fin_b);
        for pos in [upw!("abbabab", "aa"), upw!("a")] {
            assert!(dpa_fin_b.accepts(pos));
        }
        for neg in [upw!("baababbabab"), upw!("b"), upw!("aaaa", "b")] {
            assert!(!dpa_fin_b.accepts(neg));
        }

        let nba_icag_ex07_2022 = TSBuilder::without_edge_colors()
            .with_state_colors([false, false, true, true])
            .with_edges([
                (0, 'a', 0),
                (0, 'b', 0),
                (0, 'c', 0),
                (0, 'b', 1),
                (0, 'a', 3),
                (0, 'b', 3),
                (1, 'a', 2),
                (2, 'a', 0),
                (2, 'a', 3),
                (2, 'c', 1),
                (3, 'a', 3),
            ])
            .into_nba([0]);
        let dpa_icag_ex07_2022 = super::nbadet(nba_icag_ex07_2022);
        dpa_icag_ex07_2022.display_rendered().unwrap();
        assert_eq!(dpa_icag_ex07_2022.size(), 6);
    }
}
