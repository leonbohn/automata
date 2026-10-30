# CLAUDE.md

Guidance for working in this repository. See `PLAN.md` for the roadmap and known problems.

## What this is

`automata` is a single Rust crate for working with transition systems and automata over finite and infinite (omega) words. It was extracted, with history, from `leonbohn/frieda` (where it lived as `crates/automata` plus `crates/automata-core`). The former `automata-core` crate was merged in as top-level modules (`alphabet`, `word`, `math`, `dag`, plus `Color`/`Lattice`/`Void`/`Int`/`Show` at the crate root). Edition 2024, version 0.1.0, MSRV 1.88 (`rust-version`; checked by the `msrv` CI job).

Related crates that stay elsewhere: `hoars` (HOA parser, `leonbohn/hoars`, depended on from crates.io, currently 0.3) and `automata-learning` (learning algorithms, in `leonbohn/frieda`).

## Commands

```shell
cargo build --all-targets
cargo test                         # 68 unit tests, 45 doctests (some ignored)
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
./scripts/check                    # same as CI (also checks tools/bench): fmt, clippy, doc, per-feature check (needs cargo-hack), tests in three feature configurations
```

## Layout

- Foundations (formerly the `automata-core` crate):
  - `src/alphabet.rs` (+ `alphabet/`): `Symbol`, `Expression`/`Matcher`, `Alphabet`; `CharAlphabet`, `Fixed<S, N>`, `Directional`, and propositional (`PropAlphabet`, BDD-backed, used for HOA).
  - `src/word.rs` (+ `word/`): `Word`, `FiniteWord`, `OmegaWord`; `PeriodicOmegaWord`, `ReducedOmegaWord`, `NormalizedOmegaWord`; adapters (`Concat`, `Repeat`, `Skip`, `Infix`, `Rotate`). The `upw!` macro is exported at the crate root.
  - `src/math.rs`, `src/dag.rs`, `src/color.rs` (`Int`, `Void`, `Color`, `Lattice`), `src/show.rs` (`Show`).
- `src/ts.rs` and `src/ts/`: the `TransitionSystem` trait and everything around it. `TransitionSystem` only needs `edges_from` and `state_color` (algorithms that follow successors are bounded on it); `States` adds enumeration of the states (`states`, `state_count`, `contains_state`, SCCs of the whole system, `quotient`, ...). Implicit systems (`SubsetConstruction`, `MatchingProduct`) do not implement `States`; `Pointed::reachable_part` explores them into a `ReachablePart`, which does.
  - `impls/`: `LinkedTs` (the only storage so far; `u32` links, tombstones instead of swap-removal so `EdgeId`s and state indices stay stable, `compact()` renumbers) and `Det<T>`, the wrapper that makes determinism part of the type (adding an edge replaces overlapping ones). `ts::Storage` is the marker family (`Linked`, `Det<Linked>`; `Storage::Ts<Q, C>` names the concrete system) and `Sproutable::Storage` points back to it. Aliases: `NTS = LinkedTs`, `DTS = Det<LinkedTs>`. There is no `DET` const generic anymore.
  - `operations/`: lazy adapters (`recolor`, `product`, `quotient`, `reachable`, `restricted`, `reverse`, `subset`). `recolor.rs` holds the single coloring adapter `Recolor` (a `StateRecolor` and an `EdgeRecolor`, with `Keep` for the side that stays unchanged), which every `map_*`, `with_state_color` and `erase_*` returns and which serves successors and predecessors from one iterator type.
  - `edge.rs`: `EdgeRef`, the only edge reference type. `edges_from` and `predecessors` yield `ts::EdgeOf<'_, Self>`, with a borrowed color for storages and an owned one for adapters; `EdgeTuple` stays for the `Builder`.
  - `run.rs`/`path.rs`: runs with `Observer`s, `Path`, `Lasso`.
  - `connected_components/`: Tarjan SCCs, `SccDecomposition`. `reachable.rs`: reachability, minimal representatives. `builder.rs`: `Builder`.
  - Capability traits: `Deterministic`, `Pointed`, `Sproutable`, `Shrinkable`, `PredecessorIterable`; conversions in `representation.rs` (`CollectTs`, `IntoTs`).
- `examples/`: small runnable programs (`dfa`, `parity`, `transition_system`, `dot`, `hoa`), executed by CI and `scripts/check`. Examples that need an optional feature must be declared with `required-features` in `Cargo.toml` (see `hoa`).
- `src/automaton.rs` and `src/automaton/`: `Automaton<T, Sem>` pairs a TS `T` with an initial state and acceptance condition `Sem`; the word type `W` of `Semantics<T, W>` selects finite or omega semantics. Aliases `DFA<T>`, `DBA<T>`, `DPA<T, Sem>`, Moore/Mealy. `RightCongruence<T>` (in `congruence.rs`) is its own struct. `omega/` has `buchi`, `parity` (four min/max even/odd variants), `rabin`, `muller`; the `Semantics` trait defines acceptance.
- `src/congruence/` (right congruences, Cayley graphs, transition profiles), `src/minimization/partition_refinement.rs`, `src/families/` (FDFA, FWPM), `src/hoa/` (feature `hoa`), `src/dot.rs` (Graphviz/dot output and rendering), `src/random/` (feature `random`).

Edges are labeled with alphabet *expressions*; a *transition* is the concrete (state, symbol) step. Every edge is handed out as an `EdgeRef`, so adding a storage or an adapter does not add an edge type. Capabilities are layered via extra traits rather than one large trait; add a trait or blanket impl rather than extending `TransitionSystem`.

Features: `default = ["hoa"]`; opt-in: `random`, `render` (SVG/PNG via `resvg`/`layout-rs`, experimental), `graphviz` (calls the `dot` executable, implies `render`). Text `dot` output is always available.

- `benches/`: deterministic benchmarks that count instructions with `gungraun` (needs `valgrind` and the matching `gungraun-runner`), one target per area (`scc`, `ts`, `runs`, `dfa`, `dpa`), plus `wallclock` (criterion, informational). Inputs come from `benches/common` (closed-form families, no randomness) and from the Spot generated HOA files in `benches/fixtures` (`scripts/generate_benchmark_fixtures.sh`). Benchmarks must only use public API.
- `tools/bench/`: separate crate (own `Cargo.lock`, not part of the library) `automata-bench`: runs the benchmarks of one revision once (`run`, `compare`, `check-determinism`), keeps history in SQLite, and as `serve` receives GitHub webhooks and serves the read-only dashboard (htmx 4, inline SVG). `flake.nix` and `nix/` package it with valgrind and the runner and provide the NixOS module. See `docs/benchmarking.md`.

## Conventions

- `#![deny(missing_docs)]` and `deny(rustdoc::broken_intra_doc_links)` are on; README is `include_str!`ed into the crate docs, so README code blocks are doctests. They run in every feature configuration, so README examples must not need optional features (HOA examples live in the `hoa` module docs).
- Use `tracing` for logging in library code.
- Do not panic in library code: return `Result` with typed errors (`src/error.rs` has the crate-wide `#[non_exhaustive]` `Error`; domain errors such as `PropAlphabetError`, `NotPeriodicError`, `hoa::HoaError` convert into it; never use `String` as an error type); use `Error::NotYetImplemented` instead of `todo!()`/`unimplemented!()`. Existing panics are being removed (see `PLAN.md`).
- Ask before committing or pushing.
- Record every user-visible change (new API, behavior change, breaking change, removal) in `CHANGELOG.md` under "Unreleased" in the same commit.

## Known sharp edges

- `Automaton` has seven generic parameters; type errors can be long.
- Features must stay independent: code using an optional dependency needs the matching `#[cfg(feature = "...")]` (`scripts/check` builds with `--no-default-features` too).
- Many `unwrap`/`expect` calls remain in library code (see issue #7 for the audit status).
- Pull requests that are meant to change performance get the `performance` label; the benchmark service then comments before/after instruction counts. Benchmark names are tracked over time, so rename them only deliberately.
