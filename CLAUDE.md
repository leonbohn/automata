# CLAUDE.md

Guidance for working in this repository. `PLAN.md` has the roadmap, `PERFORMANCE.md` the ranked
performance opportunities. Read this file
before touching the code; follow `.md` cross-references when a task leads elsewhere.
If anything is unclear, you ask before proceeding.
Any changes are coordinated and you try not to make any bigger decisions on your own.
The whole crate should be optimized for performance as well as for ergonomics.
Work is always done in a new branch (off of `main`) and new code only lands upstream as part of a PR.
Before committing, you confer with me.

## What this is

`automata` is a single crate for transition systems and automata over finite and infinite (omega)
words, extracted with history from `leonbohn/frieda`. Version 0.2.1 is on crates.io; the tree is
heading for 0.3.0. Edition 2024, MSRV 1.88 (floor set by `biodivine-lib-bdd` and let-chains,
checked by the `msrv` CI job). Published on crates.io under the same name.

Sibling crates that stay elsewhere:

- `hoars` (crates.io, currently 0.3): HOA format parsing. Optional dependency behind the `hoa`
  feature; its `Bdd` type is shared with `biodivine-lib-bdd` (both must stay on the same major).
- `automata-learning` (in `leonbohn/frieda`): now lives in this crate as `automata::learning`
  (feature `learning`); the old crate is to be deprecated. `frieda` still has to migrate. A PR that
  changes the API should keep the migration path in mind (see CHANGELOG entries that spell out
  its migration steps).

## Commands

To ensure code quality, run the following before committing:
```shell
./scripts/check                         # everything CI runs, incl. cargo-hack per-feature check,
```

- Examples in `examples/` (`dfa`, `parity`, `transition_system`, `dot`, `hoa`) are run by CI;
  `hoa` is declared with `required-features = ["hoa"]` in Cargo.toml.
- Benches in `benches/`: `scc`, `ts`, `storage`, `runs`, `dfa`, `dpa` (gungraun, deterministic,
  inputs from `benches/common` and Spot-generated `benches/fixtures`), plus `wallclock`
  (criterion, informational). Benchmarks use public API only; names are tracked over time
  (`tools/bench` SQLite history), so rename them only deliberately.
- `bin/` holds command line tools (workspace members, `publish = false`, not part of the library):
  `oai` (reads HOA from stdin, `todpa` converts to a deterministic parity automaton) and
  `omega-learning-tasks` (generates learning tasks and runs sprout over them, see its README).
  They come from the former `frieda` repository, which this repository now is.
- `tools/bench/` is a separate crate (`automata-bench`, own `Cargo.lock`, not part of the
  library): runs/compares benchmarks, serves the dashboard. See `docs/benchmarking.md`.

## The conceptual model (read before writing any code)

Data flows through four layers; a task usually lives in exactly one of them:

1. `alphabet` — `Symbol`, `Expression`, `Matcher`, `Alphabet`. Simple alphabets (`CharAlphabet`,
   `Fixed<S, N>`, `Directional`) and BDD-backed propositional ones (`PropAlphabet`, used for HOA).
2. `word` — `Word` with `FiniteWord` and `OmegaWord` subtraits; ultimately periodic words
   `u v^ω` via the `upw!` macro (`PeriodicOmegaWord`, `ReducedOmegaWord`, `NormalizedOmegaWord`);
   adapters `Concat`, `Repeat`, `Skip`/`Infix`, `Rotate`. `Word::Kind` (`word::Finite` /
   `word::Omega`) selects finite vs omega behaviour in generic code.
3. `ts` — the transition systems, see below.
4. `automaton` — an `Automaton<T, Sem>` pairs a TS with an initial state and an acceptance
   condition; acceptance is defined by `Semantics<T, W>` implementations and the word type `W`
   of the argument selects finite or omega semantics.

Two distinctions that recur everywhere:

- **Edge vs transition:** edges are labeled with alphabet *expressions*; a transition is the
  concrete `(state, symbol)` step taken by a run. One edge covers many transitions.
- **Storage vs adapter:** storages own their states/edges (`LinkedTs`, `DenseTs`, `CsrTs`, and
  `Det<T>` wrapping any of them to make determinism part of the type); adapters are lazy views
  (`Recolor`, product, quotient, restriction, reverse, subset construction, `ReachablePart`).
  Adapters cache nothing — chain them, then materialize with `.collect::<T>()`.

## `src/` layout

- `ts.rs` + `src/ts/` — everything about transition systems:
  - `TransitionSystem` (the core trait: `edges_from`, `state_color`, `alphabet`) vs its subtrait
    `States` (enumeration: `states`, `state_count`, `contains_state`, `quotient`, ...). Implicit
    systems (`SubsetConstruction`, `MatchingProduct`) implement only the core; algorithms that
    need all states carry a `States` bound. `Pointed::reachable_part()` explores an implicit
    system once into a `ReachablePart`, which does implement `States`.
  - Capability traits: `Deterministic` (required method `edge(state, symbol)`),
    `Pointed` (initial state), `Sproutable` (grow), `Shrinkable` (remove),
    `PredecessorIterable` (`predecessors`).
  - `impls/`: `LinkedTs` (the default storage; `u32` links, tombstones instead of swap-removal,
    so `EdgeId`s stay valid; `compact()` renumbers), `Det<T>` (adding an edge replaces
    overlapping ones), `DenseTs`, `CsrTs`.
  - `ts::Storage` marker family (`Linked`, `Det<Linked>`, `Dense`, `Csr`;
    `Storage::Ts<Q, C>` names the concrete system) lets code be generic over the
    representation; `Sproutable::Storage` points back at it.
  - `operations/`: the lazy adapters. `recolor.rs` holds the single coloring adapter `Recolor`
    (parameterized by `StateRecolor`/`EdgeRecolor`, with `Keep` for the unchanged side); every
    `map_*`, `with_state_color`, `erase_*` returns one. Plus `product`, `quotient`,
    `reachable`, `restricted`, `reverse`, `subset` (`Determinize::on(&nts).run()` is the eager
    variant).
  - `edge.rs`: `EdgeRef`, the only edge reference type (storages also expose the `EdgeId` via
    `EdgeRef::id`). `edges_from`/`predecessors` yield `ts::EdgeOf<'_, Self>`.
  - `run.rs`: runs. `Deterministic::run(word)` returns a `Run` builder; `observe::<O>()`,
    `evaluate::<O>()`, `escape_prefix()`, `is_successful()`. `Observer` (with `merge`) is how
    runs collect information; see the observer structs (`NoObserver`, `Triggers`,
    `EdgeColorSet`, ...).
  - `visit.rs`: `Bfs`, `Dfs`, `BfsEdges`, `AccessWords` traversals.
  - `connected_components.rs`: `Sccs::on(&ts).compute()` / `.from(roots).compute()`, `Scc`,
    `SccDecomposition`.
  - `builder.rs`: the `Builder` (generic over the symbol type, default `char`);
    `build::<T>()` is the generic entry point, `into_dts`/`into_nts`/`into_automaton`/
    `into_dfa`/... are shorthands; every method has a `try_` twin.
  - `id_collections.rs` (`StateSet`, `StateMap`, `CompactIdMap` — bitsets/vectors for dense
    ids, hash containers otherwise), `state_index.rs` (`IdType`, `DenseId`, `EdgeId(u32)`,
    `DefaultIdType = u32`).
  - `model/`: a property-test harness for the storages (`#[cfg(test)]` only, uses proptest).
- `automaton.rs` + `src/automaton/` — `Automaton<T, Sem>`; aliases `DFA`, `DBA`, `DCW`,
  `DPA<T, Sem>`, `DRA`, `DSA`, `DMA`, `MooreMachine`, `MealyMachine`, `OmegaAutomaton<A, S = Det<Linked>>`
  and its deterministic/nondeterministic spellings. The branching is part of `Sem`
  (`branching.rs`): a bare condition is deterministic, `Existential<C>` (some run accepts) gives
  `NFA`, `NBA`, `NCW`, `NPA`, `NRA`, `NSA`, `NMA`, and `HistoryDeterministic<C>` `HDCW` (the only HD
  alias so far). A
  condition gets these by implementing `CycleCondition` (omega; drives one SCC search for
  acceptance and emptiness) or `FinalStateCondition` (finite). `Semantics` has the single method
  `output`. `omega/` holds the acceptance conditions (`buchi`, `co_buchi`,
  `parity` with four min/max even/odd variants, `rabin`, `streett`, `muller`) plus
  `OmegaAcceptanceCondition`, the enum for parsed automata whose condition is only known at
  runtime (`Parity(ParityKind, low, high)` covers the four parity variants). `problems.rs`: language problems with witnesses — `Emptiness::of(&a).witness()`,
  `Inclusion::of(&a).within(&b).counterexample()`, `Equivalence::of(&a).and(&b).holds()`,
  `Disjointness` (DFAs).
- `representation.rs`: `IntoTransitions`/`FromTransitions` (the `IntoIterator`/`FromIterator`
  of transition systems), `ts.collect::<T>()`, `collect_with_map`, `with_initial(q)`;
  `CollectPointed` has the `collect_dfa`/`collect_dpa`/... shorthands.
- `congruence/`: `RightCongruence<T>` (own struct), `Class`, `Cayley`/`RightCayley`,
  transition profiles/monoids.
- `minimization/`: Hopcroft partition refinement; `Minimize::on(&machine).run()`
  (`DFA::minimize` etc. are wrappers).
- `hoa/` (feature `hoa`): `HoaString::pop::<S>()`, `WriteHoa::to_hoa`, streams,
  `HoaError`. `dot/`: textual DOT output is always available; `render` (native, via
  resvg/layout-rs) and `graphviz` (external `dot` executable) features add images.
- `families/` (feature `families`): FDFA, FWPM, conversions.
- `learning/` (feature `learning`, implies `families`; experimental): `passive` (samples, `dfa_rpni`,
  `sprout`, `dpainf`, `PreciseDPA`) and `active` (`LStar` and the oracles); errors are
  `learning::LearningError` (converts into `Error`). Remaining panics are listed in
  `PANIC-AUDIT.md`. Imported from the former crate `automata-learning`; `docs/INTEGRATE.md`
  records how.
- `random/` (feature `random`), `partition.rs`, `math.rs` (`FxIndexMap`/`FxIndexSet` —
  deterministic hashing, keeps benchmarks reproducible), `dag.rs`, `color.rs`
  (`Color` is `Clone + Debug`; `Int = u8`, `Void`, `Lattice`), `error.rs` (crate-wide `Error`).

## Conventions

- `#![deny(missing_docs)]` and `deny(rustdoc::broken_intra_doc_links)` are on. The README is
  `include_str!`ed into the crate docs, so its code blocks are doctests that run in every
  feature configuration — README examples must not need optional features (HOA examples live
  in the `hoa` module docs).
- Do not panic in library code. Return `Result` with typed errors; `src/error.rs` has the
  crate-wide `#[non_exhaustive]` `Error` with `Error::NotYetImplemented` for missing
  constructions; domain errors (`PropAlphabetError`, `NotPeriodicError`, `hoa::HoaError`,
  `BuilderError`, `AcceptanceError`) convert into it. Never `String` as an error type.
  Panics that remain are documented with `# Panics` sections (panic audit, issue leonbohn/automata-archive#7).
- Use `tracing` for logging in library code (no `println!`).
- Features must stay independent: code using an optional dependency needs the matching
  `#[cfg(feature = "...")]`. `scripts/check` and CI build `--no-default-features` and
  `--each-feature`. Default features are just `["hoa"]`; opt-in: `families`, `random`,
  `render`, `graphviz`, `learning`.
- Record every user-visible change (new API, behavior change, breaking change, removal) in
  `CHANGELOG.md` under "Unreleased", in the same commit. The format there matters: breaking
  changes are prefixed **Breaking:**, big rewrites come with migration tables.
- Ask before committing or pushing.
- Never expose internal types in public signatures: `ts::impls` is crate-private, the exported
  surface of a storage goes through `ts::Storage`/public re-exports.

## Known sharp edges

- Nested generics (`DFA<DTS<CharAlphabet, bool, Void>>`) make compiler messages long. The
  aliases exist precisely to hide this — prefer them and add one rather than spelling types out.
- ~300 `unwrap`/`expect` remain in library code (issue leonbohn/automata-archive#7 tracks the audit); most encode
  internal invariants. Before changing one, check whether it is reachable from input.
- Lazy adapters (`Recolor`, `SubsetConstruction`, `Quotient`, ...) compute on every query and
  memoize nothing; materialize with `.collect::<T>()`. `SubsetConstruction`/`MatchingProduct`
  do not implement `States` — call `.reachable_part()` first.
- `LinkedTs` removal leaves tombstones (state indices and `EdgeId`s are never reused);
  `compact()` renumbers. Code holding `EdgeId`s across mutation must re-map.
- Nondeterministic omega automata have `accepts` and `Emptiness`, but no `Inclusion`/`Equivalence`
  and no determinization (only `NFA::determinize`). `HistoryDeterministic` is an unchecked
  promise. An `NTS` is a `LinkedTs`; `Determinize`/`subset_construction` is the bridge to
  deterministic types.
- `OmegaAcceptanceCondition::Rabin`/`Streett` → `into_dpa` returns
  `Error::NotYetImplemented`.
- Language problems on omega automata expect complete automata (a word without a run is
  ignored).
- Pull requests meant to change performance get the `performance` label; the benchmark
  service then posts before/after instruction counts.

## Testing

- Unit tests live inline (`#[cfg(test)]`); integration tests in `tests/` are currently only
  the benchmark-fixture check. `src/ts/model/` is a proptest-based model harness comparing the
  storages against a naive reference implementation.
- Doctests double as examples; when documenting a new API, write the doctest first and run
  `cargo test`. Test-module helpers like `crate::wiki_dfa()` (in `lib.rs`) exist for reuse.
- The three feature configurations are tested (`default`, `--no-default-features`,
  `--all-features`); run `./scripts/check` before handing off.
