# Integrating `automata-learning` into `automata`

Goal: move the code of `automata-learning` (about 5.5k lines, repo `leonbohn/automata-learning`)
into this crate as `automata::learning`, behind the opt-in cargo feature `learning`. Afterwards the
old crate is deprecated and `frieda` depends on `automata` directly.

**Timing:** start only after `automata 0.2.0` is released (see `RELEASE.md`). The integration then
ships as 0.2.x if it is purely additive, else as 0.3.0.

Rules from `CLAUDE.md` that apply throughout: work on a branch off `main`, land via PR, update
`CHANGELOG.md` in the same commit as each user-visible change, no panics in library code, `tracing`
instead of `println!`, features stay independent, confer before committing/pushing.

## Facts about the source crate (state at time of writing)

- Checkout: `/sam/Rust/automata-learning`, branch `refactor/automata-no-math-aliases`, depends on
  the published `automata 0.1` with features `hoa, random, render, graphviz`.
- Layout: `passive/` (`sprout.rs` + `sprout/consistency.rs`, `dpainf.rs`, `precise.rs`, `fwpm.rs`,
  `sample.rs` + `sample/{omega,finite,split,characterize,canonic_coloring}.rs`), `active/`
  (`lstar.rs`, `oracle.rs`, `mealy.rs`, `moore.rs`, `hypothesis.rs`, `observationtable.rs`),
  `priority_mapping.rs`, `prefixtree.rs`, `lib.rs`.
- Lints silenced at the crate root: `#![allow(missing_docs)]`, `#![allow(unused)]`.
- About 28 inline `#[test]`s, no `tests/`, `benches/`, `examples/`.
- Extra dependencies not (yet) in `automata`: `bimap`, `crossbeam-channel`, `tabled` (feature
  `ansi`), `owo-colors`, `alea`, `either`, `paste`. Shared already: `tracing`, `itertools`,
  `thiserror`, `rand`, `fixedbitset`.
- Overlap with this crate: `passive/fwpm.rs` (`FWPM`) and `priority_mapping.rs`
  (`FamilyOfWeakPriorityMappings`) vs. `src/families/` (FDFA, FWPM, conversions).
- Only downstream user: `frieda/bin/omega-learning-tasks`.
- It targets the old API (`StateIndex`, `CollectTs`, ...). `main` has `StateId` as the default
  state id, `CsrTs`, `Storage` markers, `Recolor`, etc.

## Status

Legend: `[x]` done, `[-]` skipped on purpose, `[ ]` open. Progress is tracked in #118.

- Phases 0 to 5 are done on `feat/learning`, apart from the open items below.
- The history is **not** imported (plain copy of `automata-learning` commit `1ed4171`), so the
  filter-repo steps of Phase 3 are skipped. The port to the 0.2 API was done in the old repo first
  (branch `phase1-baseline`), which is why Phase 4 needed only path rewrites in this crate.
- The listing of the public API (Phase 1) is skipped on purpose.
- No new dependencies were needed: `bimap`, `crossbeam-channel`, `alea`, `paste` were unused,
  `either` is replaced by `itertools::Either`, `owo-colors` and `tabled` were only cosmetic.
- `learning = ["families"]`; it does not depend on `random`, the two random-machine L\* tests are
  gated with `#[cfg(feature = "random")]`.
- Phase 5: unified on `families::FWPM` (additive changes to `families`, so 0.2.x is possible).
  `AnnotatedCongruence`/`Annotation` stay in `learning`, nothing in `congruence` overlaps.
- Phase 6 is done: no `allow(missing_docs)`/`allow(unused)` left, all public items are documented
  and the main algorithms have doctests, the panic audit is in `PANIC-AUDIT.md` (input-reachable
  panics are now `LearningError`s, see the CHANGELOG), the example `examples/learning.rs` and the
  benchmark `benches/learning.rs` exist (names: `sprout_parity` with `inf_ab_100`/`inf_ab_400`,
  `lstar_mealy` with `counting_8`/`counting_16`). Proptests: L\* learns a DFA equivalent to a random
  target, `dfa_rpni` is consistent with samples of random DFAs.
- Phase 6, skipped on purpose: the performance and the naming/ergonomics pass beyond replacing the
  default hashers by `FxIndexMap`. Candidates: the positional arguments of `dpainf` and `sprout` could
  become `Dpainf::on(..).run()`-style builders, `sprout` clones the infinity sets per candidate edge.
- Findings: `try_from_read` dropped all content lines (inverted filter, fixed); `PreciseDPA::new`
  indexed levels and classes the wrong way round (fixed); `dfa_rpni` gives up with `Threshold`
  already for some samples of random DFAs with up to 6 states (threshold `2 * max_word_len`), the
  proptest therefore only checks successful results; the test `split_up_sample` is ignored because
  its sample contradicts itself.
- Open: freezing the old repo (Phase 0), the MSRV check with 1.88 (no `rustup` on this machine),
  and the dead file `passive/sample/characterize.rs`, which is not a declared module and still
  mentions the old `fwpm::FWPM` (revive it or delete it in Phase 6).


## Phase 0 — Preconditions

- [x] `automata 0.2.0` is published and tagged.
- [x] `main` is green (`./scripts/check`).
- [x] Decide the public path: `automata::learning::{passive, active}` (recommended; keeps the old
      module names so the migration is `automata_learning::X` -> `automata::learning::X`).
- [x] Decide feature name and its dependencies (see Phase 2). Recommended: `learning`.
- [x] Open a tracking issue with this checklist (#118).
- [ ] Freeze `automata-learning`: no further feature work in the old repo, only the port.

## Phase 1 — Baseline the source crate

Do this in `/sam/Rust/automata-learning` before moving anything, so regressions are attributable.

- [x] `cargo test` and record which tests pass/are ignored.
- [x] `cargo clippy --all-targets --all-features -- -D warnings` (record existing warnings; note
      anything hidden by `allow(unused)`).
- [x] Remove `#![allow(unused)]` temporarily and list what is dead (`cargo check 2>&1 | grep unused`).
      Delete dead code in the old repo first if it is trivial, to shrink the diff of the port.
- [x] Run each algorithm once end to end and save the output as a reference: `sprout` on a small
      sample, `dpainf` on a small omega sample, `lstar` against a known DFA. These become the
      regression tests in Phase 6.
- [-] List every public item (`cargo doc` or `cargo public-api`) to know the surface being
      migrated.

## Phase 2 — Set up the branch and feature

- [x] `git switch main && git pull && git switch -c feat/learning`.
- [x] In `Cargo.toml` add optional dependencies (versions as in the old crate, bump if `automata`
      already uses a newer one):
      `bimap`, `crossbeam-channel`, `alea`, `either`, `paste`, `tabled`, `owo-colors`.
      Prefer dropping any dependency the port can do without (e.g. `either`, `paste`, `bimap` when a
      std/`indexmap` replacement is 5 lines). Fewer optional dependencies means a smaller
      feature surface.
- [x] Add the feature:
      `learning = ["random", "dep:bimap", "dep:crossbeam-channel", "dep:alea", ...]`.
      Do not make it depend on `hoa`, `render`, `graphviz` unless library code (not tests,
      examples or debugging helpers) needs them. If only tests need `hoa`/`render`, gate those tests
      with `#[cfg(feature = "hoa")]`.
- [x] Check that `tabled`/`owo-colors` are only used for pretty-printing of observation tables or
      samples. If so keep them optional under `learning`, or replace with `Display` impls to
      avoid the dependencies altogether.
- [ ] Verify the MSRV (1.88) against each new dependency: `cargo +1.88 check --features learning`.
- [x] Add `pub mod learning;` to `src/lib.rs` behind `#[cfg(feature = "learning")]`, with a
      module-level doc comment stating that the module is experimental (no stability promise until
      the next minor release).

## Phase 3 — Import the code with history

Goal: keep `git blame`/`log` for the moved files.

- [-] In a scratch clone of the old repo (never in the original):
      ```shell
      git clone /sam/Rust/automata-learning /tmp/al-import && cd /tmp/al-import
      git filter-repo --to-subdirectory-filter src/learning_import   # needs git-filter-repo
      ```
- [-] In the `automata` checkout:
      ```shell
      git remote add al-import /tmp/al-import
      git fetch al-import
      git merge --allow-unrelated-histories al-import/<branch> -m "Import automata-learning history"
      git remote remove al-import
      ```
- [-] Move into place with `git mv` (one commit, no content changes, so rename detection works):
      `src/learning_import/lib.rs` -> `src/learning.rs`, the rest -> `src/learning/`.
      Keep the sub-module layout (`passive.rs` + `passive/`, `active.rs` + `active/`).
- [x] Do **not** import: old `Cargo.toml`, `Cargo.lock`, `CLAUDE.md`, `PLAN.md`, `README.md`,
      `LICENSE.md` (same license: MIT), `.github/`, `scripts/`. Delete them in the same commit.
- [x] Alternative if history is not wanted: plain copy into `src/learning/` and say so in the
      commit message with the source commit hash (`efc0c56` or later).
- [-] The tree will not compile after this phase. That is expected; do not push this branch
      before Phase 4 compiles.

## Phase 4 — Make it compile against `main`

Work module by module, from leaves to root, running
`cargo check --features learning` after each. Suggested order:

1. `prefixtree.rs` (self-contained).
2. `passive/sample.rs` and `passive/sample/*` (data structures for words/colors).
3. `priority_mapping.rs`, `passive/fwpm.rs` (touches `families`; see Phase 5).
4. `passive/sprout.rs`, `sprout/consistency.rs`.
5. `passive/precise.rs`, `passive/dpainf.rs`.
6. `active/*` (`oracle`, `hypothesis`, `observationtable`, `mealy`, `moore`, `lstar`).

Mechanical rewrites:

- [x] `use automata::` -> `use crate::` everywhere (and `automata::prelude` -> explicit imports or
      the in-crate prelude).
- [x] `StateIndex` -> `StateId` (new default id type, `ts::state_index`), also
      `StateIndex<T>` aliases on `RightCongruence`.
- [x] `CollectTs` -> the current `representation` API (`collect::<T>()`,
      `CollectPointed::collect_dfa`/`collect_dpa`).
- [x] `automata::math::*` -> `crate::math::*` (`FxIndexMap`/`FxIndexSet`). Replace any
      `HashMap`/`HashSet` the learning code uses with these to keep results deterministic and
      benchmarks reproducible.
- [x] Edge/transition access: `edges_from`/`predecessors` now yield `ts::EdgeOf<'_, Self>`
      (`EdgeRef`); adapt pattern matches on old edge tuple types.
- [x] Colors: `Color` is `Clone + Debug`; drop any `Copy` assumptions the learning code makes.
- [x] Coloring operations go through `Recolor`/`map_*`/`with_state_color`; replace removed
      helpers.
- [x] Anything that used crate-private items of the old `automata 0.1`: use the public API only
      (never widen `ts::impls`).
- [x] `dot` helpers (`DotStateAttribute`, `DotTransitionAttribute`): the module is always
      available, no feature gate needed; image rendering (`render`/`graphviz`) stays gated.

Commit hygiene: one commit per module group, message `learning: port <module> to current API`.

## Phase 5 — Resolve the overlap with `families`

- [x] Compare `learning::passive::fwpm::FWPM` and
      `learning::priority_mapping::FamilyOfWeakPriorityMappings` with `families::{FWPM, FDFA}`:
      same concept? same invariants? same conversions?
- [x] Decide (with maintainer sign-off, this is an API decision):
      a. **Unify:** learning uses the `families` types; `families` gains whatever methods learning
         needs (`insert_pm`, `complexity`, `into_precise_dpa`, ...). Preferred.
      b. **Keep both** with different names and cross references in the docs. Only if the types
         really differ.
- [x] `families` is gated by its own feature. If learning needs it, add
      `learning = [..., "families"]`; otherwise keep it independent.
- [x] Breaking changes to `families` go in `CHANGELOG.md` as **Breaking:** and decide whether
      this forces 0.3.0 rather than 0.2.x.
- [x] Same check for `congruence::RightCongruence` and `Cayley` vs. the old `AnnotatedCongruence`
      and `Annotation`: reuse in-crate types, don't duplicate.

## Phase 6 — Quality gates (the part that makes it mergeable)

- [x] Remove `#![allow(missing_docs)]` and `#![allow(unused)]`. If the documentation backlog is
      large, a narrow `#[allow(missing_docs)]` on specific submodules is acceptable only if each
      has a tracked issue; the target is zero.
- [x] Every public item has docs; every public algorithm has a doctest (write the doctest first,
      per `CLAUDE.md`): `sprout`, `dpainf`, `lstar`, `PreciseDPA`, `Sample` constructors.
      Doctests must compile under `--features learning` (they are not run without it).
- [x] Panic audit of the imported code: `grep -rn 'unwrap()\|expect(\|panic!\|unreachable!\|\[.*\]'`
      in `src/learning/`. Convert input-reachable ones to `Result` with typed errors (add a
      `LearningError` or extend `src/error.rs`; convert it into the crate `Error`; never
      `String` errors). Document the remaining ones in `# Panics` sections and add them to
      `PANIC-AUDIT.md`.
- [x] Replace any `println!`/`eprintln!`/`dbg!` with `tracing` calls.
- [x] `crossbeam-channel` usage: check why threads are used; make sure no detached threads leak
      and that the single-threaded path still works. If concurrency is not essential, removing it
      drops a dependency.
- [x] Tests:
      - keep the ~28 inline tests; port the reference outputs from Phase 1 as regression tests;
      - add proptest properties where cheap (e.g. learned automaton is consistent with the sample;
        `lstar` against a random DFA from `random` returns an equivalent DFA, using
        `Equivalence::of(&a).and(&b).holds()`);
      - `#[ignore]` only with a comment saying why.
- [x] Examples: add `examples/learning.rs` (sprout from a sample, L\* against a target DFA) with
      `required-features = ["learning"]` in `Cargo.toml`. CI runs examples, so make sure the
      `scripts/check` loop and CI job pass the feature (see Phase 7).
- [x] Benchmarks (gungraun, deterministic): add `benches/learning.rs` with `sprout` and `lstar`
      on fixed inputs from `benches/common`; choose the benchmark names deliberately, they are
      tracked over time. Declare with `required-features`.
- [-] Performance pass: the crate is optimized for performance. Look for `clone()` of
      automata inside loops, `Vec<Vec<_>>` tables that should be dense ids, `HashMap` with default
      hasher, repeated `reachable_part()` calls on lazy adapters.
- [-] Naming/ergonomics pass: align with crate conventions (`Foo::on(&x).run()` builders,
      `try_` twins, aliases instead of spelled-out generics, `Sproutable`/`Deterministic` bounds
      instead of concrete `DTS`).
- [x] Visibility: nothing from `ts::impls` leaks into learning's public signatures.

## Phase 7 — CI and tooling

- [x] `.github/workflows/ci.yml`: the existing jobs cover `--all-features` (clippy, docs, tests)
      and `cargo hack --each-feature`, which now includes `learning`. Check that
      `--no-default-features` and every single-feature build still compile.
- [-] `msrv` job runs `--all-features` so it covers `learning`; confirm locally with
      `cargo +1.88 check --all-targets --all-features`.
- [x] `benches` job (`cargo bench --no-run`) builds the new bench; confirm it needs
      `required-features` or `--all-features`.
- [x] Examples loop in `scripts/check` and CI: `learning` is not a default feature, so either run
      the example with `--features learning` or rely on `required-features` skipping it. Add
      `cargo run -q --example learning --features learning` explicitly to both.
- [x] `nix flake check`: update `flake.nix`/`nix/` if feature sets or dependencies are enumerated
      there.
- [x] `./scripts/check` passes locally on the branch (all three feature configurations, docs
      with `-D warnings`, MSRV, examples, bench tooling).
- [-] Add the `performance` label to the PR if benchmark numbers of existing code could change
      (they should not; learning is additive).
Notes: the single-feature builds (`--no-default-features` and each of `families`, `random`, `render`,
`graphviz`, `hoa`, `learning`) compile without warnings; `cargo-hack` and `rustup` are not installed
here, so the MSRV (1.88) check is left to CI. The CI `benches` job now uses `--all-features`, since
`cargo bench --no-run` skips `benches/learning.rs` (`required-features`). The benchmark service
(`tools/bench` default list, `nix/module.nix`) is left unchanged, so `learning` is not tracked
there yet; add it deliberately if wanted. `nix flake check` passes. The `performance` label is
unnecessary, since existing code was not changed apart from additive items in `families`.


## Phase 8 — Documentation

- [ ] `CHANGELOG.md` under "Unreleased": "Added: `learning` feature with `automata::learning`
      (passive: sprout/RPNI, DPAInf, ...; active: L\*), moved from the `automata-learning`
      crate." Include a migration table:

      | before                                   | after                                              |
      |------------------------------------------|----------------------------------------------------|
      | `automata-learning = "0.1"`              | `automata = { version = "0.2", features = ["learning"] }` |
      | `automata_learning::passive::...`        | `automata::learning::passive::...`                 |
      | `automata_learning::active::...`         | `automata::learning::active::...`                  |
      | `automata_learning::FWPM` (if unified)   | `automata::families::FWPM` (state the real path)   |

- [ ] `README.md`: add the feature to the feature table (README code blocks are doctests that run
      in every configuration, so no learning example in the README itself; link to the module docs).
- [ ] Module docs for `automata::learning` with a short tour: passive vs. active, which input type
      each takes, links to examples, citations of the algorithms (RPNI, L\*, DPAInf paper).
- [ ] `CLAUDE.md`: add `learning/` to the `src/` layout section and to the feature list.
- [ ] `PLAN.md`: tick/replace the item "Switch `frieda`'s `automata-learning` ... to depend on
      this crate" with the new status.
- [ ] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features` has no broken intra-doc
      links.

## Phase 9 — Review and merge

- [ ] Open the PR against `main` (title: `Integrate automata-learning as the learning feature`).
      Large PR, so consider splitting into stacked PRs: (1) import + compile, (2) quality gates,
      (3) families unification. Each must be green on its own.
- [ ] Self-review the diff for leftover `allow`s, `dbg!`, commented-out code (`lib.rs` of the old
      crate has some), stale TODOs (triage into issues).
- [ ] Wait for CI (all jobs including `nix` and `bench-tools`).
- [ ] Merge (maintainer decides squash vs. merge commit; merge commit keeps the imported history
      readable).

## Phase 10 — Release and retire the old crate

- [ ] Follow `RELEASE.md` for the `automata` release (0.2.x if additive, 0.3.0 if `families` or
      other public API changed).
- [ ] In `automata-learning`: publish `0.1.1` (or `0.2.0`) that only changes the README and crate
      docs to say "moved to `automata`, feature `learning`" and adds
      `#[deprecated]`-style notices/`[badges] maintenance = { status = "deprecated" }`.
      Do not re-export from `automata` (that would make a dependency cycle in spirit and tie the
      old crate to new versions).
- [ ] Archive the GitHub repo `leonbohn/automata-learning` and update its README to point at
      `automata`.
- [ ] `frieda`:
      - root `Cargo.toml`: remove `automata-learning = "0.1"`, set
        `automata = { version = "0.2", features = ["learning", ...] }`;
      - `bin/omega-learning-tasks/Cargo.toml`: depend on the workspace `automata`;
      - update `use automata_learning::` -> `use automata::learning::`;
      - `cargo build`, run the binaries on a small input as smoke test.
- [ ] Close the tracking issue; note the release version in it.

## Risks and how to handle them

| Risk | Mitigation |
|------|------------|
| API drift makes the port larger than expected | Do Phase 1 and a throwaway dry run (`cargo check` on the imported tree) before committing to a timeline. |
| `families` unification forces a breaking change | Mark `families` unstable in the 0.2 docs; ship the integration as 0.3.0 if needed. |
| Hidden panics / `unused` code surface once lints are on | Budget a dedicated Phase 6; don't merge with blanket `allow`s. |
| Added dependencies bloat the crate or break MSRV | Everything optional under `learning`; check `cargo +1.88` and `cargo tree --features learning -d`. |
| Behavior regressions in the algorithms | Reference outputs from Phase 1 become regression tests; proptest against `Equivalence`. |
| Slow compile / CI time | `learning` is opt-in; only `--all-features` jobs pay for it. |
