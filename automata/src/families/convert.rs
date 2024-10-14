use automata_core::math::{self};

use crate::connected_components::SccIndex;

use super::{Alphabet, CollectTs, Deterministic, TransitionSystem, FDFA, FWPM};

impl<A: Alphabet> From<FDFA<A>> for FWPM<A> {
    fn from(value: FDFA<A>) -> Self {
        // TODO: assert that FDFA is saturated?
        let (leading, progress) = value.into_parts();

        let progress = progress
            .into_iter()
            .map(|(i, progress_dfa)| {
                let scc_dag = progress_dfa.tarjan_dag();
                let minimal_representatives = progress_dfa.canonical_naming();
                let mut classifications = math::Map::new();

                for q in progress_dfa.state_indices() {
                    let Some(mr) = minimal_representatives.get_by_left(&q) else {
                        continue;
                    };

                    if progress_dfa.is_loop_on(q, mr) {
                        classifications.insert(q, progress_dfa.is_accepting(q));
                    }
                }

                let mut coloring = math::Map::new();
                let dag = scc_dag.dag();
                loop {
                    if coloring.len() == dag.size() {
                        break;
                    }

                    'inner: for (scc_index, _scc) in dag.iter() {
                        if coloring.contains_key(&scc_index) {
                            continue;
                        }

                        let mut offset = 0;
                        let scc_classifications = scc_dag
                            .scc(SccIndex(scc_index))
                            .iter()
                            .filter_map(|q| classifications.get(q))
                            .collect::<math::Set<_>>();
                        assert!(scc_classifications.len() <= 1);
                        if let Some(&&b) = scc_classifications.first() {
                            if !b {
                                offset = 1;
                            }
                        }

                        let mut max_reachable = 0;
                        for reached_index in dag.reachable_from(scc_index) {
                            let Some(color) = coloring.get(&reached_index) else {
                                continue 'inner;
                            };
                            max_reachable = std::cmp::max(max_reachable, *color);
                        }

                        assert!(offset < 2);
                        let color = if (max_reachable % 2) != offset {
                            max_reachable + 1
                        } else {
                            max_reachable
                        };
                        coloring.insert(scc_index, color);
                    }
                }

                let mm = progress_dfa
                    .as_ref()
                    .map_edge_colors_full(|_q, _a, _c, p| {
                        let Some(scc_index) = scc_dag.get(p) else {
                            panic!("found no SCC for state {p}");
                        };
                        let Some(color) = coloring.get(&scc_index) else {
                            panic!("no color stored for SCC with index {scc_index}");
                        };
                        *color
                    })
                    .erase_state_colors()
                    .collect_mealy();
                (i, mm)
            })
            .collect();

        FWPM::from_parts(leading, progress)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn fdfa_to_fwpm() {
        todo!()
    }
    #[test]
    fn fwpm_to_fdfa() {
        todo!()
    }
}
