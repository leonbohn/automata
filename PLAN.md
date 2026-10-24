# PLAN: automata

Goal: a published, documented, well-tested general-purpose crate for finite- and omega-word automata (DFA, NFA, Moore/Mealy, Buchi, parity, Rabin, Muller, ...) with HOA interoperability.

This repo was extracted from `leonbohn/frieda` with its history. The extraction itself changed no behavior: all tests and doctests of the former `automata` and `automata-core` crates pass unchanged (68 unit, 45 doc).

## Phase 1 follow-ups (finish the extraction)

- [ ] Flatten `src/core/` into top-level modules (`automata::alphabet`, `automata::word`, `automata::math`, ...), dropping the `core` indirection. Keep `Color`, `Lattice`, `Void`, `Show` at sensible paths. This is a breaking path change; do it before 0.1.0 is released.
- [ ] Release `hoars` (extract into `leonbohn/hoars`, publish a version newer than the crates.io 0.2.0) and replace the git dependency, which currently blocks publishing.
- [ ] Switch `frieda`'s `automata-learning` and binaries to depend on this crate instead of their path copy; then delete `crates/automata` and `crates/automata-core` from `frieda`.
- [ ] Add `rust-version` (MSRV) and verify it in CI with `cargo-msrv`.
- [ ] Push `main` to `github.com/leonbohn/automata`, set up docs.rs metadata (`all-features = true`).
- [ ] Split heavy features: `default = ["hoa"]`; make `render`, `graphviz`, `random`, `petgraph` opt-in; keep text `dot` output always available.
- [ ] Remove the unused optional `clap` dependency.

## Phase 2: API redesign

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
- [ ] Un-ignore or delete every `#[ignore]` test and every `ignore`d doctest (4 unit, 6 doc).
- [ ] `criterion` benchmarks in `benches/` (product, determinize, minimize, SCC).
- [ ] CI: Linux/macOS/Windows test matrix, `--no-default-features` and `--all-features`, MSRV job, `cargo doc -D warnings`, `cargo deny`, `cargo semver-checks`, coverage. The current workflow only builds on Windows and macOS.

## Phase 5: documentation

- [ ] README: pitch, feature table, `cargo add`, runnable quick start, HOA I/O and rendering example, comparison with alternatives (Spot, `regex-automata`), badges.
- [ ] Crate-level rustdoc tour (alphabet, word, transition system, automaton, acceptance, operations) with runnable examples; examples on all major public functions.
- [ ] `examples/` (build a DFA, minimize, boolean ops, parse HOA and render, omega acceptance).
- [ ] mdBook guide in `docs/`, deployed via GitHub Pages; `CHANGELOG.md`, `CONTRIBUTING.md`.
- [ ] Keep `CLAUDE.md` in sync.

## Phase 6: release

- [ ] Publish `automata 0.1.0` (after `hoars` is released and the `core` module is flattened); set up release-plz or cargo-release; announce.
