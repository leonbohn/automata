use itertools::Itertools;
use tracing::{trace, warn};

use crate::{
    TransitionSystem,
    core::{Show, alphabet::Alphabet, math},
    families::{FDFA, FWPM},
    representation::CollectTs,
    ts::Deterministic,
};

impl<A: Alphabet> From<FWPM<A>> for FDFA<A> {
    fn from(value: FWPM<A>) -> Self {
        let (leading, progress) = value.into_parts();
        assert_eq!(leading.size(), progress.len());

        let progress = progress
            .into_iter()
            .map(|(i, pmm)| {
                let mut coloring = math::Map::new();

                let sccs = pmm.sccs();
                // preallocate, in the worst case each SCC is transient
                let mut transient = Vec::with_capacity(sccs.size());

                for (scc_index, scc) in sccs.dag().iter() {
                    let Some(&color) = scc.interior_edge_colors().iter().max() else {
                        transient.push(scc_index);
                        continue;
                    };
                    coloring.insert(scc_index, color);
                }

                for transient_scc_index in transient {
                    let color = sccs
                        .dag()
                        .reachable_from(transient_scc_index)
                        .map(|id| *coloring.get(&id).unwrap_or(&0))
                        .max()
                        .unwrap_or(0);
                    coloring.insert(transient_scc_index, color);
                }

                let pmm = pmm
                    .as_ref()
                    .with_state_color(|q| {
                        (*coloring
                            .get(&(q as usize))
                            .expect("Must have color for each state")
                            % 2)
                            == 0
                    })
                    .erase_edge_colors()
                    .collect_dfa();
                (i, pmm)
            })
            .collect();

        Self::from_parts(leading, progress)
    }
}

impl<A: Alphabet> From<FDFA<A>> for FWPM<A> {
    fn from(value: FDFA<A>) -> Self {
        // TODO: assert that FDFA is saturated?
        let (leading, progress) = value.into_parts();
        assert_eq!(leading.size(), progress.len());

        let progress = progress
            .into_iter()
            .map(|(i, progress_dfa)| {
                let scc_dag = progress_dfa.sccs();
                let minimal_representatives = progress_dfa.canonical_naming();
                let mut classifications = math::Map::new();

                for (scc_index, scc) in scc_dag.dag().iter() {
                    for state_index in scc.iter() {
                        let Some(mr) = minimal_representatives.get_by_left(state_index) else {
                            warn!("should have minimal representative for state {state_index}, unreachable?");
                            continue;
                        };
                        if progress_dfa.is_loop_on(*state_index, mr) {
                            let c = progress_dfa.is_accepting(*state_index);
                            if classifications.contains_key(&scc_index) {
                                assert_eq!(classifications.get(&scc_index), Some(&c));
                            } else {
                                classifications.insert(scc_index, c);
                            }
                        }
                    }
                }
                trace!("computed SCC classifications\n{:?}", classifications);

                let mut coloring = math::Map::new();
                let dag = scc_dag.dag();
                loop {
                    if coloring.len() == dag.size() {
                        break;
                    }

                    'inner: for (scc_index, scc) in dag.iter() {
                        trace!(
                            "considering SCC {scc_index} with states {}",
                            scc.iter().map(|q| q.show()).take(2).join(", ")
                        );
                        if coloring.contains_key(&scc_index) {
                            continue 'inner;
                        }

                        let offset = classifications.get(&scc_index).map(|b| if *b {0 } else {1 }).unwrap_or(0);
                        trace!("using offset {offset}");

                        let mut max_reachable = 0;
                        'max_reachable_color: for reached_index in dag.reachable_from(scc_index) {
                            if reached_index == scc_index {
                                continue 'max_reachable_color;
                            }
                            let Some(color) = coloring.get(&reached_index) else {
                                continue 'inner;
                            };
                            max_reachable = std::cmp::max(max_reachable, *color);
                        }
                        trace!("maximum reached color is {max_reachable}");

                        assert!(offset < 2);
                        let color = if (max_reachable % 2) != offset {
                            max_reachable + 1
                        } else {
                            max_reachable
                        };

                        coloring.insert(scc_index, color);

                        trace!("assigning {color} to SCC {scc_index}");
                    }
                }

                let mm = progress_dfa
                    .as_ref()
                    .map_edge_colors_full(|_q, _a, _c, p| {
                        let Some(scc_index) = scc_dag.scc_index_of(p) else {
                            panic!("found no SCC for state {p}");
                        };
                        let Some(color) = coloring.get(&*scc_index) else {
                            panic!("no color stored for SCC with index {scc_index}");
                        };
                        *color
                    })
                    .erase_state_colors()
                    .collect_mealy();
                (i, mm)
            })
            .collect();

        Self::from_parts(leading, progress)
    }
}

#[cfg(test)]
mod tests {
    use crate::automaton::DFA;
    use crate::ts::TSBuilder;
    use crate::{
        TransitionSystem,
        families::{FDFA, FWPM},
    };
    use automata_core::alphabet::CharAlphabet;

    #[test_log::test]
    fn fdfa_to_fwpm() {
        let alphabet = CharAlphabet::of_size(3);
        let prc = DFA::builder()
            .with_edges([
                (0, 'a', 0),
                (0, 'b', 1),
                (0, 'c', 2),
                (1, 'a', 2),
                (1, 'b', 1),
                (1, 'c', 3),
                (2, 'a', 4),
                (2, 'b', 3),
                (2, 'c', 2),
                (3, 'a', 5),
                (3, 'b', 5),
                (3, 'c', 4),
                (4, 'a', 4),
                (4, 'b', 5),
                (4, 'c', 5),
                (5, 'a', 5),
                (5, 'b', 4),
                (5, 'c', 5),
            ])
            .with_state_colors([false, true, false, false, true, true])
            .into_dfa(0);

        let dag = prc.sccs();
        let idx = dag.scc_index_of(3).unwrap();
        let scc = dag.scc(idx);
        println!(
            "{:?}\n{:?}",
            scc.interior_edges(),
            scc.interior_transitions()
        );

        assert_eq!(prc.sccs().proper_size(), 4);

        let fdfa = FDFA::trivial(alphabet.clone(), prc);
        let fwpm = FWPM::from(fdfa);

        for (word, expected) in [
            ("a", 3),
            ("bb", 2),
            ("ccc", 1),
            ("bbbbbbc", 0),
            ("bbac", 1),
            ("ca", 0),
        ] {
            assert_eq!(fwpm[0].transform(word), Some(expected));
        }
    }
    #[test]
    fn fwpm_to_fdfa() {
        let alphabet = CharAlphabet::of_size(2);
        let prc = TSBuilder::without_state_colors()
            .with_edges([
                (0, 'a', 5, 0),
                (0, 'b', 5, 1),
                (1, 'a', 4, 1),
                (1, 'b', 4, 2),
                (2, 'a', 3, 2),
                (2, 'b', 3, 3),
                (3, 'a', 2, 3),
                (3, 'b', 2, 4),
                (4, 'a', 1, 4),
                (4, 'b', 1, 5),
                (5, 'a', 0, 5),
                (5, 'b', 0, 5),
            ])
            .into_mealy(0);
        assert_eq!(prc.sccs().dag().size(), 6);
        let fwpm = FWPM::trivial(alphabet, prc);

        let fdfa = FDFA::from(fwpm);
        for no in ["", "bb", "abaabaaaaaaaaaa", "aaaaaabaaaabbbaaaaa"] {
            assert!(!fdfa[0].accepts(no));
        }
        for yes in ["baaaaa", "baabaabaaaaa", "bbbbbaaaa"] {
            assert!(fdfa[0].accepts(yes));
        }
    }
}
