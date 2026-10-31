//! Operations on deterministic parity automata: normalization, complementation, witnesses,
//! language comparison, structure and HOA input/output.

mod common;

use automata::alphabet::CharAlphabet;
use automata::automaton::{DPA, Emptiness, Equivalence, Inclusion};
use automata::hoa::WriteHoa;
use automata::representation::IntoTransitions;
use automata::ts::Sccs;
use automata::{DTS, Int, States, TransitionSystem, Void};
use common::FixtureDpa;
use gungraun::prelude::*;
use std::hint::black_box;

fn scrambled(n: usize) -> DPA {
    common::scrambled_dpa(n, 2, 8)
}
fn scrambled_k4(n: usize) -> DPA {
    common::scrambled_dpa(n, 4, 12)
}
fn chain(n: usize) -> DPA {
    common::chain_dpa(n, 8)
}

// ---- normalization -----------------------------------------------------------------------------

#[library_benchmark]
#[bench::scrambled_1000(args = (1_000), setup = scrambled)]
#[bench::scrambled_4000(args = (4_000), setup = scrambled)]
#[bench::scrambled_k4_1000(args = (1_000), setup = scrambled_k4)]
#[bench::chain_1000(args = (1_000), setup = chain)]
#[bench::chain_4000(args = (4_000), setup = chain)]
fn normalized(dpa: DPA) -> usize {
    black_box(dpa.normalized().state_count())
}

#[library_benchmark]
#[bench::ltl(setup = common::ltl_dpas)]
#[bench::synthetic(setup = common::synthetic_dpas)]
fn normalized_fixtures(dpas: Vec<FixtureDpa>) -> usize {
    black_box(dpas.iter().map(|dpa| dpa.normalized().state_count()).sum())
}

// ---- complement --------------------------------------------------------------------------------

#[library_benchmark]
#[bench::scrambled_1000(args = (1_000), setup = scrambled)]
#[bench::scrambled_4000(args = (4_000), setup = scrambled)]
#[bench::chain_1000(args = (1_000), setup = chain)]
#[bench::chain_4000(args = (4_000), setup = chain)]
fn complement(dpa: DPA) -> usize {
    black_box(dpa.complement().state_count())
}

#[library_benchmark]
#[bench::scrambled_1000(args = (1_000), setup = scrambled)]
#[bench::scrambled_4000(args = (4_000), setup = scrambled)]
fn complement_without_normalizing(dpa: DPA) -> Option<usize> {
    black_box(
        dpa.complement_without_normalizing()
            .map(|d| d.state_count()),
    )
}

#[library_benchmark]
#[bench::ltl(setup = common::ltl_dpas)]
#[bench::synthetic(setup = common::synthetic_dpas)]
fn complement_fixtures(dpas: Vec<FixtureDpa>) -> usize {
    let mut size = 0;
    for dpa in dpas {
        size += dpa.complement().state_count();
    }
    black_box(size)
}

// ---- emptiness and witnesses -------------------------------------------------------------------

#[library_benchmark]
#[bench::scrambled_100(args = (100), setup = scrambled)]
#[bench::scrambled_400(args = (400), setup = scrambled)]
#[bench::chain_100(args = (100), setup = chain)]
#[bench::chain_400(args = (400), setup = chain)]
fn accepted_word(dpa: DPA) -> bool {
    black_box(Emptiness::of(&dpa).witness().is_some())
}

#[library_benchmark]
#[bench::scrambled_100(args = (100), setup = scrambled)]
#[bench::scrambled_400(args = (400), setup = scrambled)]
#[bench::chain_100(args = (100), setup = chain)]
#[bench::chain_400(args = (400), setup = chain)]
fn rejected_word(dpa: DPA) -> bool {
    black_box(dpa.give_rejected_word().is_some())
}

#[library_benchmark]
#[bench::ltl(setup = common::ltl_dpas)]
#[bench::synthetic(setup = common::synthetic_dpas)]
fn witnesses_fixtures(dpas: Vec<FixtureDpa>) -> usize {
    black_box(
        dpas.iter()
            .filter(|&dpa| Emptiness::of(dpa).witness().is_some())
            .count()
            + dpas
                .iter()
                .filter(|dpa| dpa.give_rejected_word().is_some())
                .count(),
    )
}

// For every priority, a word whose run sees it infinitely often as the smallest one.
#[library_benchmark]
#[bench::scrambled_100(args = (100), setup = scrambled)]
#[bench::scrambled_400(args = (400), setup = scrambled)]
#[bench::chain_100(args = (100), setup = chain)]
#[bench::chain_400(args = (400), setup = chain)]
fn witness_colors(dpa: DPA) -> usize {
    black_box(
        dpa.colors()
            .filter(|&c| dpa.witness_color(c).is_some())
            .count(),
    )
}

// ---- comparing languages -----------------------------------------------------------------------

// A pair of an automaton and its normalization: equal languages, so nothing can be refuted
// early and the whole product is searched.
fn with_normalization(n: usize) -> (DPA, DPA) {
    let dpa = common::scrambled_dpa(n, 2, 8);
    let normalized = dpa.normalized();
    (dpa, normalized)
}

// An automaton and its complement: the languages are disjoint, a counterexample is found quickly.
fn with_complement(n: usize) -> (DPA, DPA) {
    let dpa = common::scrambled_dpa(n, 2, 8);
    let complement = dpa.clone().complement();
    (dpa, complement)
}

#[library_benchmark]
#[bench::normalized_25(args = (25), setup = with_normalization)]
#[bench::normalized_50(args = (50), setup = with_normalization)]
#[bench::normalized_100(args = (100), setup = with_normalization)]
#[bench::complement_25(args = (25), setup = with_complement)]
#[bench::complement_50(args = (50), setup = with_complement)]
#[bench::complement_100(args = (100), setup = with_complement)]
fn language_equivalent((a, b): (DPA, DPA)) -> bool {
    black_box(Equivalence::of(&a).and(&b).holds())
}

#[library_benchmark]
#[bench::normalized_25(args = (25), setup = with_normalization)]
#[bench::normalized_50(args = (50), setup = with_normalization)]
#[bench::normalized_100(args = (100), setup = with_normalization)]
#[bench::complement_25(args = (25), setup = with_complement)]
#[bench::complement_50(args = (50), setup = with_complement)]
#[bench::complement_100(args = (100), setup = with_complement)]
fn included_in((a, b): (DPA, DPA)) -> bool {
    black_box(Inclusion::of(&a).within(&b).holds())
}

#[library_benchmark]
#[bench::normalized_25(args = (25), setup = with_normalization)]
#[bench::normalized_50(args = (50), setup = with_normalization)]
#[bench::normalized_100(args = (100), setup = with_normalization)]
#[bench::complement_25(args = (25), setup = with_complement)]
#[bench::complement_50(args = (50), setup = with_complement)]
#[bench::complement_100(args = (100), setup = with_complement)]
fn witness_not_subset_of((a, b): (DPA, DPA)) -> bool {
    black_box(Inclusion::of(&a).within(&b).counterexample().is_some())
}

#[library_benchmark]
#[bench::complement_25(args = (25), setup = with_complement)]
#[bench::complement_50(args = (50), setup = with_complement)]
#[bench::complement_100(args = (100), setup = with_complement)]
fn witness_inequivalence((a, b): (DPA, DPA)) -> bool {
    black_box(Equivalence::of(&a).and(&b).counterexample().is_some())
}

// ---- structure ---------------------------------------------------------------------------------

#[library_benchmark]
#[bench::scrambled_1000(args = (1_000), setup = scrambled)]
#[bench::scrambled_4000(args = (4_000), setup = scrambled)]
#[bench::chain_1000(args = (1_000), setup = chain)]
#[bench::chain_4000(args = (4_000), setup = chain)]
fn sccs(dpa: DPA) -> usize {
    black_box(Sccs::on(&dpa).compute().size())
}

// The congruence that the learning algorithms ask for.
#[library_benchmark]
#[bench::scrambled_8(args = (8), setup = scrambled)]
#[bench::scrambled_16(args = (16), setup = scrambled)]
#[bench::chain_8(args = (8), setup = chain)]
#[bench::chain_16(args = (16), setup = chain)]
fn prefix_partition(dpa: DPA) -> usize {
    black_box(dpa.prefix_partition().len())
}

#[library_benchmark]
#[bench::scrambled_1000(args = (1_000), setup = scrambled)]
#[bench::scrambled_4000(args = (4_000), setup = scrambled)]
fn collect_dpa(dpa: DPA) -> DPA {
    black_box(dpa.collect())
}

#[library_benchmark]
#[bench::scrambled_1000(args = (1_000), setup = scrambled)]
#[bench::scrambled_4000(args = (4_000), setup = scrambled)]
fn map_edge_colors_collect(dpa: DPA) -> usize {
    black_box(
        dpa.map_edge_colors(|c| c / 2 as Int)
            .collect::<DTS<CharAlphabet, Void, Int>>()
            .state_count(),
    )
}

// ---- HOA ---------------------------------------------------------------------------------------

fn ltl_texts() -> Vec<String> {
    common::fixture_texts(common::LTL)
}
fn synthetic_texts() -> Vec<String> {
    common::fixture_texts(common::SYNTHETIC)
}

#[library_benchmark]
#[bench::ltl(setup = ltl_texts)]
#[bench::synthetic(setup = synthetic_texts)]
fn hoa_parse(texts: Vec<String>) -> usize {
    black_box(
        texts
            .iter()
            .map(|text| common::parse_dpa(text).state_count())
            .sum(),
    )
}

#[library_benchmark]
#[bench::ltl(setup = common::ltl_dpas)]
#[bench::synthetic(setup = common::synthetic_dpas)]
fn hoa_print(dpas: Vec<FixtureDpa>) -> usize {
    black_box(
        dpas.iter()
            .map(|dpa| dpa.to_hoa().expect("writable").len())
            .sum(),
    )
}

library_benchmark_group!(
    name = dpa;
    benchmarks = normalized, normalized_fixtures, complement, complement_without_normalizing,
        complement_fixtures, accepted_word, rejected_word, witnesses_fixtures, witness_colors,
        language_equivalent, included_in, witness_not_subset_of, witness_inequivalence, sccs,
        prefix_partition, collect_dpa, map_edge_colors_collect, hoa_parse, hoa_print
);

main!(library_benchmark_groups = dpa);
