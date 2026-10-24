# CLAUDE.md

Guidance for working in this repository. See `PLAN.md` for the roadmap and known problems.

## What this is

`automata` is a single Rust crate for working with transition systems and automata over finite and infinite (omega) words. It was extracted, with history, from `leonbohn/frieda` (where it lived as `crates/automata` plus `crates/automata-core`). `automata-core` is now the `src/core/` module. Edition 2024, version 0.1.0.

Related crates that stay elsewhere: `hoars` (HOA parser, currently a git dependency on `leonbohn/frieda`, to be released/extracted on its own) and `automata-learning` (learning algorithms, in `leonbohn/frieda`).

## Commands

```shell
cargo build --all-targets
cargo test                         # 68 unit tests, 45 doctests (some ignored)
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
./scripts/check                    # fmt + clippy + doc + test
```

## Layout

- `src/core/`: foundations (formerly the `automata-core` crate; transitional location, see `PLAN.md`).
  - `alphabet`: `Symbol`, `Expression`/`Matcher`, `Alphabet`; `CharAlphabet`, `Fixed<S, N>`, `Directional`, and propositional (`PropAlphabet`, BDD-backed, used for HOA).
  - `word`: `Word`, `FiniteWord`, `OmegaWord`; `PeriodicOmegaWord`, `ReducedOmegaWord`, `NormalizedOmegaWord`; adapters (`Concat`, `Repeat`, `Skip`, `Infix`, `Rotate`). The `upw!` macro is exported at the crate root and re-exported as `core::upw`.
  - `math`, `dag`, `Color`, `Lattice`, `Void`, `Show`.
- `src/ts.rs` and `src/ts/`: the `TransitionSystem` trait and everything around it.
  - `impls/`: `LinkedListTransitionSystem` (default; aliases `TS`, `DTS`, `NTS`), edge-list variants, `petgraph`-backed (feature `petgraph`).
  - `operations/`: lazy adapters (`map`, `product`, `quotient`, `restricted`, `reverse`, `subset`, `with_state_color`).
  - `run.rs`/`path.rs`: runs with `Observer`s, `Path`, `Lasso`.
  - `connected_components/`: Tarjan SCCs, `SccDecomposition`. `reachable.rs`: reachability, minimal representatives. `builder.rs`: `TSBuilder`.
  - Capability traits: `Deterministic`, `Pointed`, `Sproutable`, `Shrinkable`, `PredecessorIterable`; conversions in `representation.rs` (`CollectTs`, `IntoTs`).
- `src/automaton.rs` and `src/automaton/`: `Automaton<A, Z, Q, C, D, const OMEGA, const DET>` pairs a TS with an initial state and acceptance condition `Z`. Aliases `DFA`, `DBA`, `DPA`, Moore/Mealy. `omega/` has `buchi`, `parity` (four min/max even/odd variants), `rabin`, `muller`; the `Semantics` trait defines acceptance.
- `src/congruence/` (right congruences, Cayley graphs, transition profiles), `src/minimization/partition_refinement.rs`, `src/families/` (FDFA, FWPM), `src/hoa/` (feature `hoa`), `src/dot.rs` (Graphviz/dot output and rendering), `src/random/` (feature `random`).

Edges are labeled with alphabet *expressions*; a *transition* is the concrete (state, symbol) step. Capabilities are layered via extra traits rather than one large trait; add a trait or blanket impl rather than extending `TransitionSystem`.

Features: `default = ["hoa", "random", "render"]`, plus `graphviz`, `petgraph`, `implementations`.

## Conventions

- `#![deny(missing_docs)]` and `deny(rustdoc::broken_intra_doc_links)` are on; README is `include_str!`ed into the crate docs, so README code blocks are doctests.
- Use `tracing` for logging in library code.
- Inside `src/core/`, refer to siblings with `crate::core::...`.

## Known sharp edges

- `Automaton` has seven generic parameters; type errors can be long.
- `hoars` is a git dependency, so this crate cannot be published until `hoars` is released.
- Heavy rendering dependencies are in `default` features.
- ~320 `unwrap`/`expect` and ~65 `panic!` calls in library code; many `#[allow(missing_docs)]`.
