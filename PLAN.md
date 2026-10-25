# PLAN: automata

Goal: a published, documented, well-tested general-purpose crate for finite- and omega-word automata (DFA, NFA, Moore/Mealy, Buchi, parity, Rabin, Muller, ...) with HOA interoperability.

This repo was extracted from `leonbohn/frieda` with its history. The extraction itself changed no behavior: all tests and doctests of the former `automata` and `automata-core` crates pass unchanged (68 unit, 45 doc).

## Phase 1 follow-ups (finish the extraction)

- [x] Flattened `src/core/` into top-level modules (`automata::alphabet`, `automata::word`, `automata::math`, `automata::dag`) with `Color`, `Lattice`, `Void`, `Int`, `Show` re-exported at the crate root (issue #9). `automata-learning` needs matching path updates.
- [x] `hoars` 0.3.0 is released (own repo `leonbohn/hoars`); this crate depends on it from crates.io. `biodivine-lib-bdd` is on 0.6 to match (its `Bdd` type is shared via `hoars`), plus `itertools` 0.15 and `resvg`/`usvg` 0.49.
- [ ] Remaining dependency upgrades: `rand` 0.8 to 0.10 (and `rand_distr` accordingly) and `tabled` 0.16 to 0.22; both need API migrations.
- [x] Fixed `--no-default-features` (ungated `hoars` impl in `acceptance_mask.rs`, unused imports in `dot.rs`); all feature combinations build, pass clippy and tests. `scripts/check` and CI now cover it. Still to do: a full feature matrix (`cargo hack --each-feature`) in CI.
- [ ] Switch `frieda`'s `automata-learning` and binaries to depend on this crate instead of their path copy; then delete `crates/automata` and `crates/automata-core` from `frieda`.
- [x] `rust-version = "1.88"` (the floor set by `biodivine-lib-bdd` 0.6 and let-chains); verified by the `msrv` CI job and clippy's `incompatible_msrv` lint. Revisit when dependencies raise their minimum.
- [ ] Push `main` to `github.com/leonbohn/automata`, set up docs.rs metadata (`all-features = true`).
- [x] Slimmed the default features to `["hoa"]`; `render`, `graphviz` and `random` are opt-in. Text `dot` output stays always available. docs.rs builds with all features.
- [ ] Consider further feature gates for non-standard modules (e.g. `families` with FDFA/FWPM), and review the rendering on all platforms (see issues).
- [x] Removed the unused optional `clap` dependency (it created an implicit public feature).
- [x] Deleted dead code that was never compiled: `edge_lists.rs`, `petgraph_backed.rs`, `packed.rs`, together with the no-op features `petgraph` and `implementations` and the unused `petgraph` dependency (still in git history).

## Phase 2: API redesign

- [x] Introduced the crate-wide `Error` enum (`#[non_exhaustive]`, `Error::NotYetImplemented`) and `Result` alias in `src/error.rs`. `OmegaAcceptanceCondition::satisfied` and `DeterministicOmegaAutomaton::into_dpa` now return `Result`.
- [x] Typed errors replace every `Result<_, String>` and `Result<_, ()>` (#8): `PropAlphabetError`, `word::NotPeriodicError`, `hoa::HoaError`, all folded into the `#[non_exhaustive]` crate `Error`.
- [x] Panic audit, tier 1 (#7): the HOA reader and writer, acceptance masks and `into_dpa`, the `TransitionSystem` contract for unknown states (`edges_from` / `state_color`), `transitions_from`, `is_idempotent` and the builder (`try_into_*`) now return typed errors or `Option` instead of panicking. `ts::impls` internals are crate-private.
- [x] Panic audit, tier 2 (partly): `# Panics` sections for the alphabet, symbol, math, random and builder constructors.
- [ ] Panic audit, remaining: add `# Panics` docs or replace the panics in ~45 other public functions (mostly SCC/Tarjan, `ts::path`, `ts::run`, automaton witness functions and `parity::normalized`; their `unwrap`s mostly encode internal invariants) and the ~220 `unwrap`/`expect` calls overall. Open the question per module whether each is an invariant, a precondition (document) or reachable from input (error).
- [ ] Implement the conversions that currently return `Error::NotYetImplemented`: `into_dpa` for Rabin, Streett, Reachability and Safety (Rabin/Streett need a real construction such as an index appearance record), and `OmegaAcceptanceCondition::satisfied` for everything except Parity. Rabin/Streett variants of the enum carry no pairs; decide whether the enum should.
- [ ] Reduce `Automaton`'s seven parameters (remove the `OMEGA`/`DET` const bools by carrying that information in the acceptance condition and TS types). Concise aliases for `DFA`, `NFA`, `DBA`, `NBA`, `DPA`, `NPA`, `DRA`, `DMA`, `Moore`, `Mealy`.
- [ ] Add a `prelude` module.
- [ ] Replace panics in the public API with `Result`/`Option` and one crate `Error` type; shrink large error variants and drop the `result_large_err` allows.
- [ ] First-class `NFA`/`NBA` with documented `.determinize()`.
- [ ] Stop deriving `Copy` on `Automaton`; audit derives; `#[non_exhaustive]` on public enums and errors; seal traits not meant for extension.
- [ ] Review index-type genericity: support non-`usize` indices properly or simplify to a `StateId` newtype.

## Phase 3: algorithm completeness

1. Boolean operations for every acceptance type where closure exists; complement for deterministic parity, Rabin, Muller.
2. Emptiness and witness extraction (accepting word / lasso).
3. Equivalence and inclusion checks with counterexamples.
4. Minimization: Hopcroft DFA, Moore/Mealy, DPA priority reduction.
5. Acceptance conversions (Buchi/Rabin/Muller to parity) and Safra determinization.
6. Regex to NFA, `from_words` builders.
7. Differential tests against Spot via HOA.

## Phase 4: quality bar

- [ ] Remove blanket `allow(missing_docs)` (34 uses) and `allow(unused)`; document every public item.
- [ ] Integration tests in `tests/`, property tests (`proptest`): `minimize(A) ≡ A`, `A ∪ ¬A` accepts everything, HOA round trips.
- [x] No `ignore`d doctests left (README rewritten, all snippets run). Still to decide: the 4 `#[ignore]`d unit tests (3 rendering tests, see #16, and one `random` benchmark-style test).
- [ ] `criterion` benchmarks in `benches/` (product, determinize, minimize, SCC).
- [ ] CI: Linux/macOS/Windows test matrix, `--no-default-features` and `--all-features`, MSRV job, `cargo doc -D warnings`, `cargo deny`, `cargo semver-checks`, coverage. The current workflow only builds on Windows and macOS.

## Phase 5: documentation

- [x] README rewritten (pitch, feature table, install, runnable quick starts for DFAs and DPAs, lazy transition-system operations, DOT output, concepts). The HOA example lives in the `hoa` module docs (it needs the `hoa` feature, README doctests run without features). Still to do at release time: switch the install instructions from the git dependency to `cargo add automata`, add crates.io / docs.rs badges, and add a comparison with alternatives (Spot, `regex-automata`).
- [ ] Crate-level rustdoc tour (alphabet, word, transition system, automaton, acceptance, operations) with runnable examples; examples on all major public functions.
- [ ] `examples/` (build a DFA, minimize, boolean ops, parse HOA and render, omega acceptance).
- [ ] mdBook guide in `docs/`, deployed via GitHub Pages; `CHANGELOG.md`, `CONTRIBUTING.md`.
- [ ] Keep `CLAUDE.md` in sync.

## Phase 6: release

- [ ] Publish `automata 0.1.0` (after the remaining items of issue #15); set up release-plz or cargo-release; announce.

## Known issues parked for later

Performance (measure with benchmarks first, see Phase 4):
- `src/ts/connected_components/tarjan.rs`: for every back edge the stack is walked linearly (`skip_while`), which can make SCC computation quadratic; the `tee()` has an unused half.
- `src/ts/impls/linked.rs`: state removal removes edges one by one via repeated first-edge lookups.
- `src/minimization/partition_refinement.rs`: open question whether edge colors can be dropped entirely when collecting into a Moore machine.

Correctness and design:
- `From<FDFA> for FWPM` (`src/families/convert.rs`) does not check that the FDFA is saturated (documented as a precondition). The check is costly; add it later, probably as an opt-in `TryFrom`.
- `PeriodicOmegaWord` should wrap a non-empty word type instead of documenting the invariant.
- `out_edge_position` / `in_edge_position` in `linked.rs` have a "make this a match" cleanup pending.
