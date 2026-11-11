# Changelog

All notable changes to this project are documented in this file.
The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html). While the version is 0.x, minor releases may contain breaking changes.

> Issue and pull request numbers up to 0.2.1 that are written `leonbohn/automata-archive#N` refer to the
> archived repository `leonbohn/automata-archive`, which this repository replaced (the history of the
> former `frieda` is part of this repository since 0.2.1). Issues that were still open are
> `#128` to `#139` here.

## [Unreleased]
### Added
- `Alphabet::covers`, whether every symbol matches one of some expressions. `States::is_complete` uses it; propositional alphabets join the expressions (a BDD or truth-table union) and compare with the universal one instead of enumerating symbols. It no longer panics for edges with symbols outside the alphabet.
- `Builder::into_csr`/`try_into_csr` and `into_det_csr`/`try_into_det_csr` build the immutable `CsrTs` (and `Det<CsrTs>`) directly.
- Experimental (#157): `alphabet::Atoms`, the atoms (minterms) of propositional edge labels by partition refinement, `Atoms::split_edges` relabels a system to the atom alphabet (one letter per atom), and `Emptiness`, `Inclusion` and `Equivalence` have `*_by_atoms` methods for `DFA`, `DPA` and `DBA` over a `PropAlphabet`. They are slower than the regular methods in all benchmarks so far and never used implicitly.
- `Determinize::run` (and with it `NFA::determinize`) handles classes of symbols instead of single symbols for propositional alphabets with more than 5 atomic propositions, like Spot's powerset construction, as long as there are at most `256 * aps` distinct edge labels (new `Alphabet::letter_classes`, default `None`). The edges of the result are then labeled by atoms instead of valuations. `Determinized` is built without the overlap check of `DTS`, which was quadratic in the number of atoms; `Determinized::merge_edges` and the new `ts::operations::merge_parallel_edges` merge edges to the same state into one (new `Expression::union`, default `None`), which `NFA::determinize` does, like Spot. For an 8-state automaton over 10 propositions this takes about 70 ms instead of 37 s (see the benchmark `ts::determinize_propositional`).
- Parity games (#143, WP7): `ParityGame::solve` now uses tangle learning (van Dijk, 2018) and returns winning strategies with the winning regions (`Solution::strategy`); the former Zielonka solver is `ParityGame::solve_zielonka` and serves as reference. `ParityGame::letter_game` builds the letter game of a parity automaton (for a deterministic one and Adam choosing the letters, Eve wins iff the language is universal). The benchmark `game` has `tangle_learning` next to `zielonka`. Python: `solve_zielonka`, `solve_with_strategy` on the game classes and `letter_game` on `DPA`/`PropDPA`.
- Benchmark suite `benches/versus` (#143, WP9): wall-clock comparison of `automata` (through the Python bindings) with Spot (DPA equivalence and inclusion, parity games) and with Oink (parity games, Zielonka and PP+), with a check that both sides compute the same result. `automata-bench` runs it after the other benchmarks (`--versus-script`, `--no-versus`), stores it in the history and shows it on the new page `/versus` and in the detail view of a run; the NixOS option `services.automata-bench.versusScript` controls it, the package brings `maturin`, `python3`, Spot and Oink, and the default `benches` now include `nondeterministic` and `game`. New operations are added in `benches/versus/ops_*.py`, see its README.
- Differential tests of the parity game solver against `spot.solve_parity_game` (`python/tests/test_spot_games.py`).
- `ParityGame::from_pgsolver` and `ParityGame::to_pgsolver` read and write games in the PGSolver format (`GameError::PgSolver`, `PgSolverError`); in Python `from_pgsolver` and `to_pgsolver`.
- Python: the parity games `MaxEvenParityGame`, `MinEvenParityGame`, `MaxOddParityGame` and `MinOddParityGame` (`add_vertex`, `add_edge`, `solve`) and the exception `GameError`.
- Differential tests of `automata::game` against the solver [Oink](https://github.com/trolando/oink) (`tests/oink.rs`; skipped if `oink` is not found), the benchmark `game`, and the flake package `oink` (also in the dev shell). The package `oink` of nixpkgs is an unrelated DDNS client, so `nix/oink.nix` builds the solver.
- `game` module with parity games: `ParityGame<T, C>` over any `TransitionSystem` whose state colors are `Vertex { owner, priority }` (default arena `Arena`, a `LinkedTs` over a one-letter alphabet), for all four parity conditions (`MaxEvenParityGame`, `MinEvenParityGame`, `MaxOddParityGame`, `MinOddParityGame`). `ParityGame::solve` uses Zielonka's algorithm and returns a `Solution`; it fails with `GameError::NotTotal` (which converts into `Error`) if a vertex has no successor.
- Co-Büchi automata are named `DCA`, `NCA` and `HDCA` (and `into_dca`, `into_nca`, `NCA::from_dca`, ...) like the other types (acceptance condition + `A` for automaton); these names were never released.
- `Dottable` for automata with co-Büchi (`DCA`), Rabin, Streett and Muller conditions, for the three
  parity conditions other than min even and for the nondeterministic `NFA`, `NBA`, `NCA`, `NPA`,
  `NRA`, `NSA` and `NMA`: edges show their color, the accepting states of an `NFA` are double
  circles and the pairs (Rabin, Streett) or sets (Muller) of the condition are written in an extra
  `acceptance` node. `DotStyle::dot_header_statements` adds statements to the header of the graph
  and `MullerCondition::sets` returns the sets of the condition.
- Python bindings in `python/` (distribution `automatars`, import name `automata`, built with maturin,
  `abi3-py311`; #143, WP4 and WP5). Every automaton class exists over a `CharAlphabet` and, with
  the prefix `Prop`, over a `PropAlphabet`:
  - `CharAlphabet`, `PropAlphabet`, `OmegaWord(prefix, period)`.
  - Deterministic: `DFA` (union, intersection, complement, minimize, language problems with
    counterexamples), `DBA`, `DCA`, `DPA` (min even; complement, inclusion, equivalence),
    `DPAMaxEven`, `DPAMinOdd` and `DPAMaxOdd` (`to_min_even`, `complement`, `to_hoa`, `from_hoa`),
    `DRA`, `DSA`, `DMA`, `MooreMachine` and `MealyMachine` (minimize, bisimilarity). Nondeterministic: `NFA`
    (`determinize`), `NBA`, `NCA`, `NPA`. All have `sccs()`, `states()`, `edges_from(q)`.
  - HOA input/output (`to_hoa`, `from_hoa`, `automata.parse_hoa`, `parse_hoa_all`) for Büchi,
    co-Büchi, all four parity conditions, Rabin and Streett (`PropDRA`/`PropDSA` number the sets
    of acceptance sets of the edges as colors), conversions
    (`NFA.from_dfa`, `NBA.from_dba`, `NCA.from_dca`, `NPA.from_dpa`, `DPA.from_dba`, `DPA.from_dca`),
    builders (`DFABuilder`, `automata.builders`).
  - DOT and SVG output (`to_dot`, `_repr_svg_`) for every class.
  - Complements that only change the condition: `DBA.complement()` (a `DCA`), `DCA.complement()`,
    `DRA.complement()` (a `DSA` with every pair `(fin, inf)` swapped), `DSA.complement()` and
    `DMA.complement()` (all nonempty sets of edge colors that are not in the family; `ValueError`
    for more than 16 colors). `DBA.streamlined()`.
  - Exceptions: `automata.Error` with subclasses mirroring `crate::Error`; `NotYetImplemented` is
    `NotImplementedError`. Generated `.pyi` stubs (`cargo run --bin stub_gen`), `PANIC-AUDIT.md`
    lists the guards for Python input.
  - A `python` job in CI and an optional Python step in `scripts/check`. The package is installed
    from GitHub (see `python/README.md`).
- Nondeterministic automata as aliases over one generic semantics, `automaton::Existential<C>`:
  a word is accepted if *some* run satisfies the acceptance condition `C` (#143). `NBA`, `NCA`,
  `NPA` (with the parity variant as a parameter), `NRA` and `NMA` for infinite words, `NFA` for
  finite ones. Any condition that implements `CycleCondition` (infinite words) or
  `FinalStateCondition` (finite words) works, so a new condition gets its nondeterministic
  automaton for free. Infinite words are decided on the product with the word's cycle by an SCC
  decomposition, which is linear for Büchi, co-Büchi, parity and Rabin conditions, polynomial for
  Streett (`StreettCondition`) and exponential in the number of colors for Muller and for the
  Streett case of `OmegaAcceptanceCondition`.
- History-deterministic automata as a promise in the type: `automaton::HistoryDeterministic<C>`
  (same acceptance as `Existential<C>`) with the aliases `HDFA`, `HDBA`, `HDCA`, `HDPA`, `HDRA`
  and `HDMA`. `assume_history_deterministic()` turns a nondeterministic automaton into one
  (unchecked, the checks come with WP8 of #143), `into_existential()` drops the promise.
  `Emptiness` and HOA output work as for nondeterministic automata.
- `Automaton::map_acceptance(f)` replaces the acceptance condition, e.g.
  `dba.map_acceptance(Existential)` is the `DBA` as an `NBA`.
- The co-Büchi condition `CoBuchiCondition` with `DCA` and `NCA`.
- The Streett condition `StreettCondition<C>`, dual to `RabinCondition<C>` and built from the same
  `RabinPair`s (`fin` disjoint from the colors seen infinitely often, or `inf` meets them; all pairs
  have to hold, no pair accepts everything), with `DSA` and `NSA`. It implements `Semantics` and
  `CycleCondition`, so `accepts`, `Emptiness` and HOA output (`HoaAcceptance`) work; emptiness
  refines the SCCs by removing the `fin` colors of violated pairs.
- Builder shortcuts `into_nba`, `into_dca`, `into_nca`, `into_npa` and the generic
  `into_nondeterministic_automaton(initial, acceptance)`, each with a `try_` twin.
- `Emptiness` with an accepted word as witness for every nondeterministic omega automaton
  (`Automaton<T, Existential<C>>`) and for `DCA`, `DRA` and `DMA`; `Emptiness`, `Inclusion` and
  `Equivalence` for `NFA` (via `NFA::determinize`). Inclusion and equivalence of nondeterministic
  omega automata are not offered, they need a determinization or complementation that does not
  exist yet.
- Benchmark target `nondeterministic`: acceptance of lassos and emptiness for NPA, NBA, NCA, NRA
  and NMA, and acceptance on fixtures read with the `Linked` storage. `automata-bench` runs it by
  default.
- `automaton::ParityKind` (`MinEven`, `MaxEven`, `MinOdd`, `MaxOdd`) for the four variants of the
  parity condition, with `is_max` and `is_even`. `AcceptanceError::PriorityOverflow` and
  `HoaError::InconsistentAcceptance` are new (both enums are `#[non_exhaustive]`).
- HOA output (`HoaAcceptance`) for `CoBuchiCondition` (so `DCA`, `NCA`, `HDCA`) and
  `RabinCondition<Int>` (`DRA`, `NRA`, every edge color is the one acceptance set of its edge);
  `RabinCondition::pairs`. Muller automata have no HOA form.
- `Storage::Semantics<C>`: the semantics of a condition on a storage, `C` for the deterministic
  storages and `Existential<C>` for `Linked`.

### Changed
- **Breaking:** `CsrTs` is now a real compressed sparse row system: edges (expression, color, target) are stored sorted by source behind one offset per state, so it is **nondeterministic**, works for **any `Alphabet`** (not only `IndexedAlphabet`) and no longer needs a slot per state and symbol. The incoming edges are collected on first use of `predecessors`. Migration: a deterministic `CsrTs<A, Q, C>` is now `Det<CsrTs<A, Q, C>>` (`Deterministic` is only implemented there; lookups scan the row of a state instead of indexing), the storage marker `Csr` is nondeterministic and `Det<Csr>` is the deterministic one; `EdgeId`s are positions in the sorted edge list, no longer `state * k + symbol_index`. Use `DenseTs` when constant-time lookup on a small indexed alphabet matters.
- **Breaking:** (#156) `PropExpression` uses [oxidd](https://github.com/OxiDD/oxidd) instead of `biodivine-lib-bdd` for more than 6 atomic propositions (truth tables below). All BDDs live in one global manager, so equality, hashing and cloning are cheap and independently built expressions can be combined. No BDD type appears in the public API any more; the manager panics if its 2^24 nodes are exhausted. Labels are written and parsed in HOA syntax (`0 & !1`, `t`, `f`); `PropExpression::try_new`/`new`, `proposition` and `unsatisfiable` are new, as are `PropAlphabetError::{InvalidExpression, UnknownProposition}` and `HoaError::{UnknownProposition, UnresolvedAlias}`. The text of a written label can differ from before (same meaning). `PropAlphabet` no longer keeps a lock-protected set of expressions. Requires `hoars` 0.5 and Rust 1.91.
  | 0.2 | 0.3 |
  |---|---|
  | `PropExpression::from_parts(n, bdd)`, `from_bdd(bdd)` | `universal`, `unsatisfiable`, `proposition`, `!`/`&`/`\|`, or `PropExpression::new(n, "0 & !1")` |
  | `PropExpression::new(n, "x_0 & !x_1")` | `PropExpression::new(n, "0 & !1")` (HOA syntax), fallible: `try_new` |
  | `into_bdd()` | `sat_vals()`, `to_hoa_label()` |
  | `PropSymbol::as_bdd_valuation` / `from_bdd_valuation` | `as_bools` / `from_bools` |
  | `hoa::HoaExpression`, `hoa::LabelExpression::Expression` | removed (hoars 0.5), `Label` derefs to `AbstractLabelExpression` |
  | `HoaError::InvalidLabel(String)` | `HoaError::UnknownProposition`, `HoaError::UnresolvedAlias` |
  | MSRV 1.88 | 1.91 |
- `Equivalence` and `Inclusion` of deterministic parity and Büchi automata build the product once (equivalence used to build it twice) and store its edges, so edge labels (BDD intersections on propositional alphabets) are computed once and not again in every refinement round; 10 to 40 % fewer instructions on the `dpa` benchmarks.
- `PropExpression` stores expressions over at most 6 atomic propositions as truth tables (a `u64`) instead of BDDs: conjunction, disjunction, overlap and matching are bit operations, equality and hashing are integer comparisons. Larger expressions still use BDDs; `from_parts`, `from_bdd` and `into_bdd` convert. For these small expressions `sat_vals`/`symbols` yield the symbols in ascending order of their raw values. 2 to 5 times fewer instructions on the `dpa` benchmarks over HOA fixtures.
- **Breaking:** `NFA<T>` is `Automaton<T, Existential<ReachabilityCondition>>`; `NfaCondition` is
  gone. Code that names the alias is unaffected, `NfaCondition` becomes
  `Existential(ReachabilityCondition)`.
- **Breaking:** an `OmegaAutomaton<A, Linked>` (`NondeterministicOmegaAutomaton`, what HOA input
  with the `Linked` storage gives) has the semantics `Existential<OmegaAcceptanceCondition>`, so it
  accepts words (before, it had no `accepts`). Its `acceptance()` is wrapped accordingly, use
  `.0` for the condition. Implementors of `Storage` have to add `type Semantics<C>`.
- **Breaking:** `Semantics` has a single method `output(&self, ts, initial, word) -> Option<Output>`
  instead of the associated type `Observer` and the methods `observe` and `evaluate`, so that
  semantics no longer have to be phrased as the observation of a single run (#143). Observers
  stay the way deterministic semantics look at their run. `nfa::SomeRunAccepts`, which only
  existed to satisfy the old trait, is gone.

  | Before | After |
  |---|---|
  | `type Observer = O;` plus `fn observe(..)` and `fn evaluate(observed)` | `fn output(&self, ts, initial, word) -> Option<Self::Output>` |
  | `sem.evaluate(sem.observe(ts, q, w)?)` | `sem.output(ts, q, w)` |
- **Breaking:** the parity condition of `OmegaAcceptanceCondition` carries its `ParityKind`:
  `Parity(ParityKind, low, high)`; `MaxParity` is gone. `satisfied`, `into_dpa` (a DPA is
  min-even, so priorities are renumbered, `AcceptanceError::PriorityOverflow` if the result does
  not fit into an `Int`), HOA input and HOA output work for all four kinds. HOA input reads the
  kind and the number of sets from `acc-name: parity <min|max> <even|odd> <n>` (before, every
  parity automaton was read as min even); a missing, malformed or inconsistent name is
  `HoaError::InconsistentAcceptance`. HOA output writes the name and the matching formula, and
  `HoaAcceptance` exists for `MaxEvenParityCondition`, `MinOddParityCondition` and
  `MaxOddParityCondition` like for `MinEvenParityCondition`.

  | Before | After |
  |---|---|
  | `Parity(low, high)` | `Parity(ParityKind::MinEven, low, high)` |
  | `MaxParity(low, high)`, `high` even | `Parity(ParityKind::MaxEven, low, high)` |
  | `MaxParity(low, high)`, `high` odd | `Parity(ParityKind::MaxOdd, low, high)` |
  | `acc-name: parity` without kind and sets | add `min even <n>` (or the actual kind) |

  `MaxParity` accepted when `high - max` was even, i.e. when `max` had the parity of `high`; this
  is the table's second and third row.
- The dependency `hoars` is 0.4. It validates the header while parsing, so a missing `Acceptance:`
  item is a parse error (`HoaError::Parse`) instead of `HoaError::MissingAcceptanceSets`, which now
  only occurs for headers built by hand. Since `hoars` no longer caps labels at six variables, HOA
  input accepts up to 31 atomic propositions (the limit of `PropAlphabet`) instead of 6.

### Fixed
- Python: binary operations (`equivalent_to`, `included_in`, counterexamples, `product`-style methods of DFAs, machines and NFAs) compared alphabets by size only, so automata over the same atomic propositions in another order (as Spot writes them) or over other characters silently gave wrong answers. They now raise `ValueError` unless the alphabets are equal. `PropAlphabet` implements `PartialEq`/`Eq` (same propositions in the same order).
- `DFA::minimize`, `MooreMachine::minimize`, `MealyMachine::minimize` and `Minimize::on(..).run()`
  kept the unreachable states (merged into classes), although the result is documented as the
  minimal machine. They are removed now, and the states of the result are numbered in the order in
  which a breadth-first search from the initial state discovers them, so the initial state is `0`.
  **Breaking:** the result can have fewer states than before and other state numbers; this also
  applies to `DPA::streamlined`. The benchmark results of the minimization benchmarks (`dfa`)
  may change, as the quotient is built from the reachable states only.
- `DPA::give_rejected_word` (and `rejected_word()` in Python) returned `None` for automata that
  are not universal if the rejecting loop can only be reached through edges of a smaller priority:
  the way to the loop was searched in the automaton without these edges.
- HOA input ignored state-based acceptance (`State: 0 {0}`), so the automaton got no acceptance
  sets on the edges of that state and accepted another language. The sets of a state are now put on
  all its outgoing edges (united with the sets of the edge, so parity automata with a set on the
  state and on the edge are still an `AcceptanceError`).
- Products (`ts_product`, `MatchingProduct`) only paired edges with equal expressions. Over a
  `PropAlphabet`, where edges may be labeled with any formula (`[t]`, `[0]`, ...), this lost
  transitions: `Inclusion`/`Equivalence` and their counterexamples, `DPA::prefix_partition`,
  union and intersection gave wrong answers for automata with edges that are not labeled by
  single valuations (for example, a non-empty DBA was reported as included in an empty one). The
  product now has an edge for each pair of overlapping edges, labeled with the intersection of the
  expressions, for which `Expression` has the new method `intersection`.
  **Breaking:** custom implementations of `Expression` have to implement `intersection`;
  `EdgeRef::expression` no longer returns a reference with the lifetime of the system but one
  that is bound to the edge, as an edge can own a computed expression (`EdgeRef::with_expression`).
- The HOA writer put no parentheses around the pairs of Rabin and Streett conditions with two or more pairs (`(Fin(0)) | (Inf(1)) & ...`), so the written formula meant something else and could not be read back. `RabinPair` has the getters `fin()` and `inf()`.
- `OmegaAcceptanceCondition::into_dpa` converted co-Büchi and safety automata to the wrong
  language when edges of acceptance set `0` and edges outside of it both occur infinitely often
  (the priority `0` for the good edges won). The bad edges now get priority `1` and all others `2`.
- HOA input reads `acc-name: co-Buchi` (it was rejected although the output writes it). An edge
  or `Start:` item that refers to a state that is not in the body panicked when the header had no
  `States:` item, it is now `HoaError::UnknownState`.
- HOA output of Rabin and Streett conditions declares enough acceptance sets for the edges (before,
  only the sets of the pairs, which made the output invalid if an edge was in a larger set) and
  only writes `acc-name: Rabin n` if the condition is the standard one over exactly `2n` sets.

## [0.2.1] - 2026-11-04

### Added

- New opt-in feature `learning` with the module `automata::learning`: the code of the `automata-learning` crate (passive: sprout, DPAInf, precise DPA; active: L\*), imported by plain copy of its commit `1ed4171` and ported to this crate. The module is experimental. It needs no dependencies besides the feature `families` (the dependencies `bimap`, `crossbeam-channel`, `alea`, `either`, `paste`, `tabled` and `owo-colors` of the old crate are not needed). Two L\* tests that use random machines need the feature `random`.
- The algorithms of `automata::learning` return typed errors instead of panicking: `LearningError` (convertible into `Error`) for `dfa_rpni`, `infer_precise_dpa`, `dpa_rpni`, `LStar::infer`, `MealyOracle::new`, `MooreOracle::new`, `OmegaSample::split`, `SplitOmegaSample::infer_forc`, `SetSample::insert`, `ConsistencyCheck::consistent_automaton`, `AnnotatedCongruence::canonic_coloring` and `PreciseDPA::new`/`TryFrom<FWPM>`. The remaining panics are listed in `PANIC-AUDIT.md`. Migration from `automata-learning`: add `?`/`unwrap()` to the calls above, `dba_rpni` returns `Error::NotYetImplemented`, `PreciseDPA::from(fwpm)` is `PreciseDPA::try_from(fwpm)`, `OmegaSample::try_from_read` now keeps the lines of the sample (it dropped them).
- Migration from the crate `automata-learning`:

  | before | after |
  |--------|-------|
  | `automata-learning = "0.1"` | `automata = { version = "0.2", features = ["learning"] }` |
  | `automata_learning::passive::...` | `automata::learning::passive::...` |
  | `automata_learning::active::...` | `automata::learning::active::...` |
  | `automata_learning::passive::fwpm::FWPM` | `automata::families::FWPM` |
  | `fwpm.into_precise_dpa()` | `PreciseDPA::try_from(fwpm)` |

  The crate root of `automata-learning` (its `prefixtree`, `priority_mapping` and so on) is `automata::learning` as well.
- Example `learning` and benchmark `learning` (both need the feature `learning`). The benchmark tool builds the features that the selected bench targets require, runs the target `learning` by default, and the stacked chart of the dashboard backfills benchmarks that were added later with their first value (dashed line at the commit that added them, #137).
- `families::Family::leading` and `Family::iter`, and `families::FWPM::complexity` (the number of distinct priorities of the most complex class). The learning code builds on `families::FWPM` instead of having its own type: the `FWPM` of `automata-learning` (one `MooreMachine` per class) is `families::FWPM` here (one `MealyMachine` per class, whose edge colors are the priorities), and `AnnotatedCongruence::canonic_coloring` returns such a Mealy machine. `into_precise_dpa` is `PreciseDPA::from(fwpm)`.

## [0.2.0] - 2026-11-03

### Fixed

- `PropSymbol::from_bools` is now the inverse of `as_bools` (it used the opposite bit order, so
  `from_bools(s.as_bools()) != s`). Symbols enumerated from an expression change their raw value
  accordingly.
- `Inclusion`/`Equivalence` on `DPA`s and `DBA`s missed counterexamples whose cycle can only be
  reached over edges with a smaller priority than the ones on the cycle.
- Writing a `DPA` in the HOA format with a least priority above 0 produced an invalid file (edges
  labeled with sets outside of the declared `Acceptance` range); the sets now always are `0..=max`.

### Changed

- **Breaking:** the default state id of `LinkedTs`, `DenseTs`, `CsrTs` and everything built on them
  (`DTS`, `NTS`, `DFA`, ...) is now the newtype `ts::StateId` instead of `u32`, so that states
  cannot be mixed up with edge ids, colors or other integers (leonbohn/automata-archive#111). `ts::DefaultIdType` is an
  alias for it. `StateId` prints like the number it wraps (`Display` and `Debug`), so DOT output
  and error messages are unchanged.

  | Before | After |
  |---|---|
  | `ts.successor(0, 'a')` | `ts.successor(q(0), 'a')` |
  | `ts.add_edge((0, 'a', 1))` | `ts.add_edge((q(0), 'a', q(1)))` |
  | `let n: u32 = ...; ts.edge(n, a)` | `ts.edge(StateId::from(n), a)` |
  | `state as usize` | `state.into_usize()` (trait `DenseId`) |
  | `u32::from(state)`, `StateId::from(n)` | to and from the raw `u32` |

  `Builder` keeps taking plain `u32` literals (`Builder::...with_edges([(0, 'a', 1)])`,
  `into_dfa(0)`); they are converted when the system is built. Likewise `Compaction::state` and
  `BuilderError` work with `StateId`.

- **Breaking:** API consistency (leonbohn/automata-archive#109).
  - `DRA` and `DMA` default to `Int` (`u8`) colours instead of `usize`, like `DPA`.
  - `Word::FINITE` is removed; use `Word::Kind` (`word::Finite`/`word::Omega`) instead. The
    redundant `assert!(W::FINITE)` checks in `FiniteWord`/`OmegaWord` methods are gone, the types
    already guarantee it.
- `Scc::maximal_loop_from` no longer relies on `unwrap`s for its bookkeeping: the queue of the
  remaining interior transitions is read through one `match`, and the states whose transitions
  are exhausted are dropped there. The remaining `expect`s check the precondition that the states
  of the SCC are mutually reachable and are documented with a `# Panics` section, as are the
  invariant checks of `DPA::prefix_partition`, `DPA::witness_color` and `DPA::normalized`
  (whose note moved from prose into the `# Panics` section). `Scc::new` now points at
  `maximal_loop_from` in addition to `state_colors` (leonbohn/automata-archive#108).
- Panic audit, completed (leonbohn/automata-archive#108): every remaining `panic!`, `assert!`, `unwrap` and `expect` in
  a public function is either documented with a `# Panics` section (programmer-error
  preconditions such as empty alphabets, empty cycles, incomplete transition systems, states
  outside the system), a `debug_assert` or the guard of an internal invariant whose message
  names the invariant (storages, Hopcroft refinement, `compact`, `Scc::state_colors`, the
  normalization procedure). No signature changes were needed: of the panics reachable from
  public API, only `Scc::maximal_loop_from` on an SCC assembled with `Scc::new` from indices
  that are not strongly connected can fire, and panicking is the documented choice there.

### Added

- `NFA`, a nondeterministic finite automaton over an `NTS` (`Automaton<T, NfaCondition>`): `accepts`
  checks whether some run ends in an accepting state, `NFA::determinize` returns an equivalent
  `DFA` (subset construction). `NBA` is left for later. `Automaton::accepts`/`transform` no longer
  require `T: Deterministic`; the `Semantics` implementations carry that bound where needed.
- `automata::prelude`: `use automata::prelude::*;` brings the traits (`TransitionSystem`, `States`,
  `Deterministic`, `Pointed`, `Sproutable`, ...), `Builder`, `q`/`StateId`, `DTS`/`NTS`, the
  automaton aliases, the language problems, `Minimize`, `Determinize`, `upw!` and `Dottable` (plus the HOA
  reader/writer with the `hoa` feature) into scope.
- Crate-level documentation with a tour of the layers (alphabet, word, transition system with
  storages, traits, adapters and `collect`, automaton and acceptance, problems), all with runnable
  examples.
- `ts::StateId` and the shorthand `ts::q(n)` (`q(3)` is the state `q_3`).

- Property tests (`tests/properties.rs`) for DFAs, DPAs, DBAs, Moore and Mealy machines and HOA
  round trips: minimization keeps the language, `A ∪ ¬A` is universal, `A ∩ ¬A` is empty,
  De Morgan, complementation of DPAs, validity of the witnesses of the language problems (leonbohn/automata-archive#110).
- `minimization::Minimize`: `Minimize::on(&machine).run()` minimizes a `DFA`, `MooreMachine` or `MealyMachine`. The result is built directly from the Hopcroft partition, without a `Quotient` and without collecting `Vec` colors. `DFA::minimize`, `MooreMachine::minimize` and `MealyMachine::minimize` remain as wrappers (leonbohn/automata-archive#57).
- `ts::operations::Determinize`: `Determinize::on(&nts).run()` is the eager subset construction. It returns `Determinized`, a `DTS` (initial state `0`) together with the subset of original states of each state (leonbohn/automata-archive#57).
- Language problems with witnesses: `automaton::{Emptiness, Inclusion, Equivalence}` for DFAs, DBAs and DPAs (and `Disjointness` for DFAs, which does not build the intersection), e.g. `Emptiness::of(&dpa).witness()`, `Inclusion::of(&a).within(&b).counterexample()` and `Equivalence::of(&a).and(&b).holds()` (leonbohn/automata-archive#56).
- `ts::Sccs`, the SCC decomposition as one problem type: `Sccs::on(&ts).compute()` decomposes all states (needs `States`), `Sccs::on(&ts).from(roots).compute()` the part reachable from the roots. One implementation, an iterative Tarjan over `CompactIdMap`; a path of 10^6 states does not overflow the stack and it is 10 to 25 percent faster than the best previous variant on every benchmark shape (leonbohn/automata-archive#55, leonbohn/automata-archive#23).
- `representation::IntoTransitions` and `FromTransitions`, the `IntoIterator` and `FromIterator` of transition systems, with `Parts` (alphabet, states, edges, initial state). `ts.collect::<T>()` and `ts.collect_with_map::<T>()` (which also returns the numbering of the states as a `CompactIdMap`) build any storage (`LinkedTs`, `Det<LinkedTs>`, `DenseTs`, `CsrTs`) or automaton from any source in one pass. Owned storages hand out their states and edges without cloning, `&T` yields clones, and `Recolor`, `RestrictByStateIndex`, `ReachablePart` and automata pass the parts of the system they wrap on, so `ts.map_edge_colors(f).erase_state_colors().collect::<DTS<..>>()` has no intermediate system. Whether a system has an initial state is part of the type (`IntoTransitions::Initial` is `()` or the state index): `ts.with_initial(q).collect::<DFA>()`. Collecting an owned deterministic system is about 1.7 times as slow as `clone` (it was 6 to 11 times) (leonbohn/automata-archive#54).
- `representation::CollectPointed`: the shorthands `collect_dfa`, `collect_moore`, `collect_mealy`, `collect_dba`, `collect_dpa` and `collect_right_congruence` for pointed systems, each a single `collect`.
- `CompactIdMap::from_states`.
- Rabin and Streett conditions are read from HOA (`acc-name: Rabin n` / `Streett n`, one `Fin` set and one group of `Inf` sets per pair) and written with an `acc-name` when the pairs use the standard layout (leonbohn/automata-archive#52).
- `Semantics` for `OmegaAcceptanceCondition`: `accepts`/`transform` work on every deterministic omega automaton (`OmegaAutomaton`), for all conditions including Rabin and Streett. A run with malformed acceptance sets (see `satisfied`) is rejecting (leonbohn/automata-archive#52, leonbohn/automata-archive#6).
- `OmegaAcceptanceCondition::Rabin` and `Streett` carry their pairs (`Vec<RabinPair<Int>>`; Rabin: `Fin(fin) & Inf(inf)` for some pair, Streett: `Fin(fin) | Inf(inf)` for every pair). `satisfied` evaluates them; `into_dpa` for them is still open (#128, leonbohn/automata-archive#6, leonbohn/automata-archive#52).
- `hoa::output::HoaAcceptance`: the acceptance condition decides how the `Acceptance` header and the sets of an edge are written. Implemented for `BuchiCondition`, `MinEvenParityCondition` and `OmegaAcceptanceCondition`, which now also writes co-Büchi, reachability, safety, max parity, Rabin and Streett (leonbohn/automata-archive#52).
- `dot::DotStyle`: the acceptance condition decides how an automaton is drawn. Nondeterministic omega automata and DBAs are now `Dottable` (leonbohn/automata-archive#52).
- `Builder::build::<T>()` and `try_build::<T>()` build any growable transition system (`LinkedTs`, `Det<LinkedTs>`, `DenseTs`, ...); whether overlapping edges are an error is decided by the target (`Storage::DETERMINISTIC`). Shorthands for the default storage: `into_dts`, `into_nts`, `into_dts_with_initial`, `into_nts_with_initial` and `into_right_congruence`, and `into_automaton(initial, acceptance)` for every acceptance condition (leonbohn/automata-archive#51).
- `Builder` is generic over the symbol type (default `char`), so alphabets like `Fixed<usize, N>` can be built. New: the traits `alphabet::FromSymbols` (creates a `SimpleAlphabet` from its symbols; implemented for `CharAlphabet` and `Fixed`), `ts::IntoBuilderEdge`, the error `alphabet::WrongAlphabetSize` and `BuilderError::Alphabet`. `Fixed<S, N>` now implements `SimpleAlphabet` (leonbohn/automata-archive#51).
- `ts::Storage`, a marker family for the representation of owned transition systems (`Storage::Ts<Q, C>`, `try_from_linked`), with the storages `Linked` and `Det<Linked>`, and `ts::Det`, see the changes below.
- `EdgeRef::id` and `EdgeRef::with_id`: the `EdgeId` of an edge in its storage, `None` for edges of adapters. It is ignored by equality, ordering and hashing.
- `States`, a subtrait of `TransitionSystem` for finite systems whose states can be enumerated, and `Pointed::reachable_part` / `operations::ReachablePart`, which explores everything reachable from the initial state of an implicit system once and provides `States` (with constant time `contains_state`) for it (leonbohn/automata-archive#44).
- `ts::EdgeRef`, the single edge reference type: source, target, expression and a `Cow` color, with the type alias `ts::EdgeOf<'a, T>` for the edges of a transition system. Used by successors and predecessors of all storages and adapters (leonbohn/automata-archive#48).
- `ts::operations::Recolor`, one adapter for state and edge colors, built by `map_state_colors`, `map_edge_colors`, `map_edge_colors_full`, `with_state_color`, `erase_state_colors`, `erase_edge_colors` and `erase_colors`. It is parameterized by a `StateRecolor` and an `EdgeRecolor` implementation; `Keep` leaves a color as it is, closures and the wrappers `StateColorFn`, `ColorFn`, `EdgeFn` and `Provided` compute a new one. Like the adapters of `Iterator`, it is lazy and caches nothing (leonbohn/automata-archive#48).
- Rendering with an installed graphviz, mirroring the native backend: `Dottable::try_svg_graphviz`, `try_data_url_graphviz` and `render_graphviz` (PNG), next to the existing `try_svg`, `try_data_url` and `render` (features `graphviz` and `render`).
- `dot::open_in_viewer` and `dot::svg_to_data_url` as public helpers.
- `Dottable::dot_initial_state`: the initial state is marked in the DOT output by an arrow without source (an `init` node with an edge into the initial state). Implemented for DFAs, right congruences, Moore and Mealy machines and DPAs.
- `RenderError::DotNotFound` and `RenderError::DotFailed { status, stderr }` for problems with the `dot` executable.
- `examples/dot.rs` takes `--show` and `--show-graphviz` to open the rendered automaton in a viewer.
- Deterministic benchmarks that count instructions with gungraun (`scc`, `ts`, `runs`, `dfa`, `dpa`; `cargo bench`, needs valgrind) on closed-form inputs and on 22 DPAs generated with Spot (`benches/fixtures`, `scripts/generate_benchmark_fixtures.sh`), and a criterion target for wall-clock times. There is no randomness in the benchmarks.
- Benchmark tracking (see `docs/benchmarking.md`): `tools/bench` runs and compares the benchmarks (one execution per revision, 2 % threshold on instruction counts), a Nix flake provides it and a NixOS module that benchmarks `main` and pull requests labelled `performance` on a dedicated machine.
- README: table of the rendering functions, a recommendation of `graphviz`, and the prerequisites; crates.io and docs.rs badges.
- Cargo feature `families` (not a default feature) for the module `families` (FDFA, FWPM and their conversions) (leonbohn/automata-archive#17, leonbohn/automata-archive#58).
- `Display` for `InvertibleChar`, `PropSymbol`, `PropExpression`, `MinimalRepresentative`, `AcceptanceMask` and `TransitionMonoid` (replaces `Show`).
- `ts::WordKind`, which lets `WordTs` read finite and omega words with the same implementations.

### Changed

- **Breaking:** `ts::Shrinkable::trim_from` removes nothing if the source state does not exist instead of panicking. `Show::show_collection` has a default implementation (the elements in braces) instead of `unimplemented!()`. The conversions between `DeterministicOmegaAutomaton<PropAlphabet>` and `<CharAlphabet>` renumber the states instead of asserting that they are contiguous. Dot output replaces unexpected characters of an identifier with `_` instead of panicking, and the `Debug` output of a `Path` and the dot attributes of a state no longer panic. `Scc::maximal_loop_from`, the edge, state and transition table helpers no longer unwrap states that do not exist. Assertions of internal invariants (families, transition profiles, `normalized`) are `debug_assert`s, a `FDFA` that is not saturated logs a warning in the conversion to a `FWPM` instead of panicking (leonbohn/automata-archive#7).
- **Breaking:** `ReachedEdgeColor` observes an `Option` of the edge color, and `Run::last_edge_color` and `Mealy` outputs return `None` for the empty word instead of panicking (leonbohn/automata-archive#7).
- **Breaking:** `Automaton::congruent` and `RightCongruence::congruent` return `Option<bool>`, `None` if one of the words has no run. `DFA::separate` returns `None` if one of the states does not exist. `PropAlphabet::size` no longer has a panicking conversion. `# Panics` sections for `is_accepting`, `LazyMinimalRepresentatives::get`, `Quotient::unwrap_class_representative`, `OmegaIteration::new`; invariants that do not depend on the input are `debug_assert`s (leonbohn/automata-archive#7).
- **Breaking:** `Path::reached_state_color` returns an `Option`, and `Path::empty_in` and `Path::empty_in_with_capacity` return `None` for a state that is not colored in the system; `Path::extend_in` no longer panics (and leaves the path unchanged) if the target is not colored. `Scc::maximal_loop_from` returns `None` for a state outside the SCC. `# Panics` sections for `Scc::new`, `Scc::state_colors`, `SccDecomposition::{first, singleton_nontrivial}`, `Path::extend_with`, `EscapePrefix::{with_length, escape_symbol}` (leonbohn/automata-archive#7).
- **Breaking:** `Alphabet::make_expression` is a provided method on top of the new required `Alphabet::try_make_expression`, which returns `None` for a symbol outside the alphabet (leonbohn/automata-archive#7).
- **Breaking:** `Color::reduce` returns `None` for an empty iterator instead of panicking (leonbohn/automata-archive#7).
- **Breaking:** `math::FxIndexMap` no longer implements `ProvidesStateColor`, as it panicked for states without an entry. Wrap the map in `DefaultIfMissing` (leonbohn/automata-archive#7).
- `RenderError::PngEncodingError` and `RenderError::RenderToSvgError` carry a boxed error instead of a `String` (leonbohn/automata-archive#7).
- `Quotient::new` computes the edges and state colors of all classes once, so `edge` and `state_color` do not allocate. `Quotient::new` and `TransitionSystem::quotient` now require `Deterministic`; a partition that is not a congruence no longer panics when an edge is looked up, the target of the first state of the class is used (leonbohn/automata-archive#57).
- Inclusion and equivalence of DPAs decompose one product into strongly connected components (and only the components that cannot be used right away again) instead of one decomposition per pair of priorities (leonbohn/automata-archive#56).
- `DPA::prefix_partition` no longer copies the automaton and does not run an equivalence check per pair of states: it decomposes the product of the automaton with itself once and finds all inequivalent pairs by a backwards search. `DPA::separate` no longer collects its arguments (leonbohn/automata-archive#56).
- `DFA::union`, `intersection` and `negation` return lazy views and no longer collect; use `reachable_part().collect_dfa()` (or `collect_dfa()` where the view has `States`) to materialize. `union` and `intersection` no longer provide `States` (leonbohn/automata-archive#56).
- **Breaking:** `Scc` stores its states as a sorted `Vec` (it dereferences to a slice, `contains` is a binary search) and no longer caches edge sets. `interior_edges` and `border_edges` iterate over edge references (`EdgeOf`) computed on request, `interior_edge_colors` iterates over the colors (one per edge) and `minimal_representative` returns an owned `Option` (the access words are still computed once per decomposition). `SccDecomposition::fold_edge_colors` takes owned colors. The `EdgeColor: Hash + Eq` bounds are gone (leonbohn/automata-archive#55).
- **Breaking:** `CollectTs` and `IntoTs` are replaced by `IntoTransitions`/`FromTransitions` and `CollectPointed`, see above. Removed: `collect_dts`, `collect_dts_and_initial`, `collect_dts_preserving`, `trim_collect_pointed`, `into_dts*`, `into_moore*`, `into_mealy`, `into_dfa*`, `into_dpa*`, `into_dba*`, `into_right_congruence` (use `collect`, `with_initial` and, to drop colors, `erase_state_colors`/`erase_edge_colors`; `Builder::into_dfa(q)` and friends stay), `Sproutable::sprout_from_ts` and `sprout_from_ts_with_bijection` (use `collect` and `collect_with_map`), `CsrTs::from_ts` (use `collect`) and `LinkedTs::zip_state_indices`, `unzip_state_color`, `old_to_new` and `new_to_old` (use `collect_with_map`) (leonbohn/automata-archive#54).
- **Breaking:** `DPA::normalized` and `DPA::streamlined` return a `DPA<DTS<..>>` instead of an opaque type, so the result can be collected or modified. The edges of a collected `LinkedTs` keep the order in which the source lists them (collecting a reference used to reverse it).
- **Breaking:** `WriteHoa` is implemented once, for `Automaton<T, Z>` with `Z: HoaAcceptance<T>`; the per-automaton hook methods are gone. `write_hoa` and `to_hoa` return a `HoaError` instead of panicking or discarding it. `OmegaAcceptanceCondition::write_hoa` is replaced by `HoaAcceptance::write_acceptance` (leonbohn/automata-archive#52).
- **Breaking:** `Dottable` is implemented once, for `Automaton<T, Z>` with `Z: DotStyle<T>` (`RightCongruence` keeps its own impl). Moore and Mealy machines are named `Moore` and `Mealy` instead of `DPA`, and the Mealy initial state is no longer additionally marked in its label; it already has the initial arrow (leonbohn/automata-archive#52).
- The HOA output of edges that belong to no acceptance set no longer has `{1}` (DBAs) or a trailing space; Büchi edges that are not accepting are written without a set (leonbohn/automata-archive#52).
- **Breaking:** `OmegaAcceptanceCondition` is no longer `Copy` (the Rabin and Streett variants hold their pairs) (leonbohn/automata-archive#52).
- The `Parity` condition of a parsed HOA automaton has `high = Acceptance sets - 1` (it was one too large) (leonbohn/automata-archive#52).
- **Breaking:** the `Builder` no longer has one method per target type: `build::<T>()` is the generic entry point and `into_dts`, `into_nts`, `into_automaton` etc. are shorthands for the default storage (22 public methods in total including the `try_` twins, 10 of them for the five automata helpers). `Builder` gained a third type parameter for the symbols. Every method has a `try_` twin that returns a `BuilderError`. The edges of a built system are iterated in the order in which they were given (before, `into_dts` and `into_nts` iterated them in reverse); `EdgeId`s run in the opposite order (leonbohn/automata-archive#51).

  | Before | Now |
  |---|---|
  | `into_nts()` | `into_nts()` (unchanged) |
  | `into_dts()` | `into_dts()` (unchanged) |
  | `into_nts_with_initial(i)` | `into_nts_with_initial(i)` (unchanged) |
  | `into_dts_with_initial(i)` | `into_dts_with_initial(i)` (unchanged) |
  | `into_right_congruence(i)` | `into_right_congruence(i)` (unchanged) |
  | `into_right_congruence_bare(i)` | `into_dts().with_initial(i).erase_colors().into_right_congruence()` |
  | `into_dfa(i)`, `into_dba(i)`, `into_dpa(i)`, `into_moore(i)`, `into_mealy(i)` | unchanged, now one-liners over `into_automaton(i, acceptance)` |
  | `try_into_*` | `try_into_dts`, `try_into_nts`, `try_into_dts_with_initial`, `try_into_nts_with_initial`, `try_into_right_congruence`, `try_into_automaton`, `try_into_dfa`, ... |
  | any other storage, for example `DenseTs` | `build::<DenseTs<CharAlphabet, _, _>>()` / `try_build::<T>()` (the alphabet must be named because it is no longer fixed to `CharAlphabet`) |
- `DPA::normalized` keeps its recoloring in a table indexed by `EdgeId` instead of a hash map keyed by (state, expression), and removes edges by id.
- **Breaking:** the `DET` const generic is gone. Determinism is a property of the type: `Det<T>` wraps a transition system and replaces overlapping edges when an edge is added. `DTS<A, Q, C>` is `Det<LinkedTs<A, Q, C>>` and `NTS<A, Q, C>` is `LinkedTs<A, Q, C>`; the alias `TS` is removed. `Builder` lost its `DET` parameter (`into_ts` and `try_into_ts` are gone, use `into_nts` or `into_dts`), `LinkedTs::try_into_deterministic` returns `Det<LinkedTs>`, and `into_nondeterministic` is `Det::into_inner`.
- **Breaking:** `Sproutable::add_edge` returns the `EdgeId` of the new edge instead of the overwritten edge. A `Det` replaces all overlapping edges; `Builder::try_into_dts` still reports `OverlappingEdge`. `Sproutable` gained `edge_color_mut`, `state_color_mut` (`set_state_color` is provided on top of it) and the associated type `Storage`. `Shrinkable` gained the required `remove_edge(EdgeId)`; the `remove_edges_*` methods other than `remove_edges_to` are provided on top of `remove_edge` and `EdgeRef::id`.
- **Breaking:** `OmegaAutomaton<A, S>`, `HoaAutomatonStream<R, S>`, `HoaString::pop::<S>()` and the functions of `hoa::input` are generic over a storage (`Det<Linked>` or `Linked`) instead of `const DET: bool`. `OmegaAutomaton::try_from(HoaRepresentation)` exists for both storages.
- **Breaking:** `LinkedListTransitionSystem` is renamed to `LinkedTs` and has a new layout: endpoints and list links are `u32` with a `u32::MAX` sentinel (24 instead of 80 bytes of bookkeeping per edge). Removing an edge or a state leaves a tombstone instead of swap-removing, so `EdgeId`s and state indices stay valid and are never reused. New: `insert_edge` (returns the `EdgeId`), `remove_edge`, `edge_by_id`, `edge_color_mut`, `state_color_mut`, `edge_count`, `edge_bound`, `compact` (returns a `Compaction` with the old-to-new renaming) and `check_consistency` (was `verify_state`). `filter_swap_remove_edges` is now `filter_remove_edges`; `predecessors` of a removed or unknown state is `None` instead of a panic; `from_parts`/`into_parts` and the public `LinkedListTransitionSystemState`/`Edge` types are gone.
- **Breaking:** `IndexType` and `ScalarIndexType` are replaced by `IdType` and `DenseId` (`from_usize`, `into_usize`, `into_id` instead of `into_index`), implemented for `u8`, `u16`, `u32` and `usize`. `IdType` is no longer implemented for every type: `ProductIndex` and custom ids need an (empty) `impl IdType`. Added the newtype `EdgeId(u32)` (leonbohn/automata-archive#41).
- Added `TransitionSystem::state_bound`, overridden by the linked list and forwarded by the wrappers, and the id containers (hash based fallback uses `FxBuildHasher`) `StateSet`, `StateMap` and `CompactIdMap`, which use bitsets and vectors for dense ids and hash containers otherwise. They replace the B-tree and hash based visited sets in `Reachable`, `LengthLexicographicMinimalRepresentatives`, omega runs, the `run::StateSet` observer (now derefs to `ts::StateSet` instead of `BTreeSet`; iteration order is only sorted for dense ids), both Tarjan variants, Kosaraju and the Hopcroft style partition refinement (leonbohn/automata-archive#41).
- The bitset dependency is `fixedbitset` instead of `bit-set`.
- **Breaking:** removed the type aliases `math::OrderedSet`, `math::OrderedMap` and `math::Bijection` and the reexports `math::ordered_set` and `math::ordered_map`; use `BTreeSet`, `BTreeMap`, `bimap::BiBTreeMap` and `std::collections::{btree_set, btree_map}` directly (leonbohn/automata-archive#64).
- **Breaking:** `math::Set` and `math::Map` are renamed to `math::FxIndexSet` and `math::FxIndexMap` and use the deterministic `rustc_hash::FxBuildHasher` instead of a randomly seeded one, so iteration order and benchmark instruction counts are reproducible. They are created with `default()` instead of `new()`. The hash maps in the SCC and normalization code use the same hasher.
- **Breaking:** `math::Partition` moved to `partition::Partition`.
- **Breaking:** `TransitionSystem::state_color` returns `Option<Cow<'_, StateColor>>`, and `EdgeRef::color` returns `&C` (with `EdgeRef::into_color` handing out the `Cow<'_, C>`). Stored colours (linked list, Cayley graphs, quotient edges, product edges) are returned as `Cow::Borrowed`, so reading them does not clone; colours computed by map views, products of states, quotients and subset constructions are `Cow::Owned`. The `StateColorSet` and `EdgeColorSet` observers only clone colours they have not seen yet. Migration: `.color()` now gives a reference, so use `.color().clone()`, `*e.color()` (for `Copy` colours) or `e.into_color().into_owned()` where an owned value is needed; compare with `ts.state_color(q).as_deref() == Some(&c)`.
- **Breaking:** one edge reference type instead of one per storage and adapter (leonbohn/automata-archive#48). The associated types `TransitionSystem::EdgeRef` and `PredecessorIterable::PreEdgeRef` are gone; `edges_from` and `predecessors` yield `ts::EdgeOf<'_, Self>`, i.e. `EdgeRef<'a, StateIndex, EdgeExpression, EdgeColor>`, with the public methods `source`, `target`, `expression`, `color` (a `&C`), `into_color`, `with_color`, `map_states`, `reversed` and `into_tuple`. The trait `IsEdge` and the types `Edge`, `EdgeReference`, `TransitionOwnedColor`, `QuotientTransition`, `ProductTransition`, `ProductPreTransition`, `MappedEdge`, `MappedPreEdge`, `MappedTransition`, `MappedPreTransition` are removed, and `EdgeRef::reversed` replaces the wrapper that reversed the edges of a reversed system. `EdgeRef` borrows the color if the storage stores it (linked list, Cayley) and owns it if the adapter computes it (recolor, product, quotient, subset construction); `EdgeRef::into_tuple` clones the expression, so it is only used where an owned edge is wanted. `EdgeTuple` and `IntoEdgeTuple` stay for the `Builder`, so two edge types remain: the borrowed `EdgeRef` and the owned tuple.
- **Breaking:** the four recoloring adapters `MapEdges`, `MapEdgeColor`, `MapStateColor` and `WithStateColor` (with their four mirrored pre-edge iterators) are replaced by `operations::Recolor`, which serves successors and predecessors from one iterator type (leonbohn/automata-archive#48). `operations::EraseColors` is now a `Recolor` over `Void` colors, and `EraseStateColors`/`EraseEdgeColors` are the aliases of the two halves. `map_*` and `erase_*` return a `Recolor<..>` instead of the old named adapters. `ProvidesStateColor`, `DefaultIfMissing` and `UniformColor` are unchanged, `with_state_color` wraps them in `Provided`. The closures of `map_*` are lazy: they run on every access to a color and nothing is cached, so materialize with `collect`. As a consequence `IntoTs` is implemented for `Recolor` instead of for the four old adapters, and `DFA::from_ts` returns a `DFA<Recolor<D, Provided<DefaultIfMissing<..>>>>` instead of `DFA<WithStateColor<..>>`.
- `MatchingProduct` no longer collects the edges of the right component into a `Vec` per call: `ProductEdges` asks the right system for a fresh edge iterator per edge of the left one, so iterating the product does not allocate, and a deterministic `edge` lookup stays `edge` on both sides (leonbohn/automata-archive#48).
- `Deterministic::edge` of `LinkedListTransitionSystem` follows the out-list of the state directly instead of building an `edges_from` iterator, which is what made single-symbol lookups expensive (leonbohn/automata-archive#48).
- **Breaking:** the filter of `RestrictByStateIndex` is no longer implemented for `Vec`: a `Vec` needs a linear scan per edge, while `ts::StateSet` (constant time for dense ids) and `BTreeSet` are supported (leonbohn/automata-archive#48).
- **Breaking:** `Path::transitions`, `Path::into_transitions`, `Lasso::recurrent_transitions` and `Lasso::into_recurrent_transitions` yield `(source, expression, color, target)` tuples instead of the removed `Edge` type (leonbohn/automata-archive#48).
- **Breaking:** `Color` is relaxed to `Clone + Debug`; it no longer implies `Eq` and `Hash`, so colours such as `f64` can be used for building and running. APIs that need them (`StateColorSet`, `EdgeColorSet`, Muller and Rabin semantics, minimization, SCC border edges, `color_range`, ...) carry `Eq`/`Hash` (or `PartialEq`) bounds themselves. `Builder::into_dts_with_initial` no longer requires `Hash + Eq` for the edge colour.
- **Breaking:** new module `ts::visit` with the traversals `Bfs`, `Dfs`, `BfsEdges` and `AccessWords`. `Reachable<_, FULL_EDGE>` (and the module `ts::reachable`) is removed: `reachable_state_indices*` and `reachable_states*` return `Bfs`, the edge variant is `reachable_edges_from` (`BfsEdges`). `AccessWords` runs one lazy breadth-first search, stores a parent and a symbol per state (memory O(n) instead of one cloned word per queue entry) and reconstructs length-lexicographically minimal access words on demand; the expressions of the edges of a state are expanded to `(symbol, target)` pairs and sorted by symbol, so the result no longer depends on the order in which edges are iterated and is also right for expressions that match several symbols. `LengthLexicographicMinimalRepresentatives`, `minimal_representative`, `word_from_to`, `canonical_naming*` and `LazyMinimalRepresentatives` are built on it. `Scc::minimal_representative` shares one search between all SCCs of a decomposition instead of running one per SCC. Traversals of a state that does not exist yield nothing instead of panicking (leonbohn/automata-archive#43).
- **Breaking:** `Automaton<A, Z, Q, C, D, const OMEGA, const DET>` is now `Automaton<T, Sem>`: the alphabet and colours are determined by the transition system `T`, `OMEGA` is gone and `Automaton` no longer derives `Copy` (leonbohn/automata-archive#46). `Semantics<T, W>` takes the word type `W` instead of the const bool and has a new required method `observe` that runs the word; the word type selects finite or omega semantics, so a single `accepts`/`transform` serves both and `W` is inferred from the argument. The aliases take a transition system (`DFA<T = DTS<CharAlphabet, bool, Void>>`, `MooreMachine<T>`, `MealyMachine<T>`, `DBA<T>`, `DPA<T, Sem>`, `DRA<T>`, `DMA<T>`, ...), so `DFA<A>` becomes `DFA<DTS<A, bool, Void>>`. `FiniteWordAutomaton`, `InfiniteWordAutomaton` and all `Into*`/`Collect*` aliases are removed (use the plain alias with the transition system as argument). `MooreSemantics` and `MealySemantics` are no longer generic. `Max*`/`MinOdd` parity conditions now implement `Semantics`, too.
- **Breaking:** `RightCongruence<T>` is a dedicated struct (transition system, initial state and the lazily computed minimal representatives) instead of an `Automaton` with `LazyMinimalRepresentatives` as acceptance condition. The cache is discarded when the congruence is modified through `Sproutable` or `Shrinkable` (leonbohn/automata-archive#46).
- `DPA::normalized` stores the recoloring in a `HashMap` instead of a linearly searched `Vec` and collects the transition system only once (leonbohn/automata-archive#39).
- Removing edges and states of a `LinkedListTransitionSystem` (`remove_edges_from`, `remove_edges_to`, `remove_edges_between`, `remove_edges_from_matching`, `remove_edges_between_matching`, `remove_state`) walks the edge lists of the states involved instead of scanning all edges, so the cost is proportional to the degree. The order of the returned edges may differ.
- `IntoTs::into_dfa_with_initial` only requires `Deterministic<StateColor = bool>` instead of `Congruence`, since the initial state is given explicitly.
- **Breaking:** `display_rendered` and `display_rendered_graphviz` now write an SVG to a temporary file and open it with the default program of the system (`xdg-open` on Linux, `open` on macOS, `start` on Windows) instead of piping a PNG to ImageMagick's `display`. This works on Wayland. The `IMAGE_VIEWER` environment variable is still honored, the program is now called with the path of the file instead of reading from stdin. The temporary file is not deleted.
- **Breaking:** the `graphviz` feature no longer implies `render`; it does not pull in `layout-rs`, `resvg` and `usvg` anymore.
- **Breaking:** `RenderError` is `#[non_exhaustive]`, `PngDisplayError` was renamed to `Io` and `NonZeroExit` was replaced by `DotFailed`. Variants that belong to the native backend only exist with the feature `render`.
- `render_to_file_name` (feature `graphviz`) takes the output format from the file extension (default `png`) and no longer uses a temporary file.
- Data URLs are encoded with padded base64 and keep the XML prolog of the SVG.
- `src/dot.rs` was split into the module `dot` (`attributes`, `impls`, `native`, `graphviz`, `render`); the public paths are unchanged.

- Dependencies: `rand` 0.8 to 0.10 (the `random` module uses `rand::rng()` and `RngExt`) and `tabled` 0.16 to 0.22. No public signatures change; the output of the transition tables is unchanged.
- **Breaking:** `TransitionSystem` is split into a small core and the new subtrait `States` (leonbohn/automata-archive#44). The core needs `edges_from`, `state_color` and `alphabet` (plus the associated types and the optional `state_bound`); algorithms that only follow successors (runs, `Bfs`/`Dfs`/`AccessWords`, `reachable_*`, `word_from_to`, `minimal_representatives_iter*`, `canonical_naming*`, `is_reachable_from`, `sccs_kosaraju`, `reachable_sccs_from`) and all adapters (`map_*`, `erase_*`, `restrict_state_indices`, `edge_color_restricted`, `with_state_color`, `with_initial`, `subset_construction*`) stay on it. Everything that needs all states moved to `States`, which you have to import (`automata::States`), and some methods were renamed:
  - `state_indices` -> `States::states`, `StateIndices` -> `StatesIter`, `state_indices_with_color` -> `states_with_color`, `size` -> `state_count`, `contains_state_index` -> `contains_state`, `is_stateless` and `is_empty` -> `has_no_states` (the old `is_empty` clashed with language emptiness such as `DBA::is_empty`), `state_indices_vec` -> `states().collect()`.
  - Moved unchanged: `transitions`, `is_edgeless`, `edge_colors`, `edge_colors_unique`, `is_deterministic`, `is_complete`, `find_by_color`, `contains_state_color`, `quotient`, `sccs`, `sccs_recursive`. `state_bound` stays on `TransitionSystem` since traversals use it to pick dense containers.
  - `SubsetConstruction` and `MatchingProduct` are implicit and no longer implement `States` (nor `IntoTs`/`CollectTs`/`Dottable`). Call `reachable_part()` first, e.g. `a.ts_product(b).reachable_part().collect_dfa()` (this also leaves out unreachable pairs, which `collect_*` used to include). `Cayley`, `RightCayley` and `WordTs` are finite and implement `States`.
  - `Sproutable`, `Shrinkable`, `Dottable`, `CollectTs`, `IntoTs` and `WriteHoa` require `States`; the finite-state algorithms (SCCs of a whole system, minimization, `Family`, `TransitionMonoid`, `Cayley::new`, `DPA`/`DBA`/`DFA` methods that enumerate states) carry a `States` bound.
  - `Deterministic::build_transition_table` takes the states to print as first argument so that it works for implicit systems.
  - `contains_state` is constant time for the linked list, `Automaton`, `RightCongruence`, `ReachablePart`, `Quotient`, `Cayley`, `RightCayley`, `WordTs` and all adapters (they forward to the wrapped system; `RestrictByStateIndex` also checks its filter).
  - `Deterministic::successor`, `edge_color` and `is_loop_on` no longer check `contains_state_index` (`edges_from` already returns `None` for unknown states); `is_loop_on` and `is_reachable_from` no longer panic on unknown states.
- **Breaking:** `Symbol` and `Expression` require `Display` instead of `Show`. `FiniteWord::as_string` needs no extra bound anymore. `Debug` of `ReducedOmegaWord` and `PeriodicOmegaWord` is available for `Display` symbols.
- **Breaking:** `ts::WordTs` lost its `const FINITE: bool` parameter (`WordTs<A, W>`); finite and omega words share one implementation. The predecessors of the first state of a purely periodic word now contain the edge that closes the loop.
- **Breaking:** `congruence::StateNaming` and `LazyMinimalRepresentatives` dereference to a `BTreeMap` instead of a `BiBTreeMap` (the dependency `bimap` is gone). `RightCongruence::mr_to_state` looks the state up through the index stored in the representative.
- `math::{almost_equal, continuous_bernoulli_*, sample_continuous_bernoulli}` need the feature `random`, which is now the only feature that pulls in `rand`.
- Plain-text tables (`Debug` of `SubsetConstruction`, `Display` of `TransitionMonoid`) are rendered by a small internal helper; the `tabled` and `owo-colors` dependencies are gone and the tables are no longer colored or drawn with box characters.

### Removed

- The scattered language-problem methods are replaced by the problem types (see Added): `DFA::equivalent`, `symmetric_difference_is_empty`, `symmetric_difference_word`, `intersection_is_empty`, `give_word`, `is_empty_language`, `DPA::give_accepted_word`, `witness_colors`, `witness_inequivalence`, `witness_not_subset_of`, `language_equivalent`, `included_in`, `includes` and `DBA::give_word`, `is_empty` (leonbohn/automata-archive#56).
- **Breaking:** `States::sccs`, `sccs_recursive` and `TransitionSystem::reachable_sccs_from`, `sccs_kosaraju` (use `Sccs`; `from` follows edges out of the given states instead of ignoring them), the functions `tarjan_scc_iterative*`, `tarjan_scc_recursive`, `kosaraju` and `Tarjan`, `Scc::interior_transitions`, `border_transitions` and `is_empty`, and the `tracing::info!` timing in the hot loop. Kosaraju was not faster than `Sccs::from` on any benchmark shape (leonbohn/automata-archive#55, leonbohn/automata-archive#23).
- **Breaking:** `Deterministic::edge(state, symbol)` is now the required method and takes a symbol instead of a `Matcher`; the default that scanned `edges_from` is gone, so no provided method of `Deterministic` calls `edges_from` any more and lazy views can no longer recurse between the two. Views implement `edge` and derive `edges_from` with `DeterministicEdgesFrom`; storages implement both. `Deterministic::successor_index` is renamed to `successor` (leonbohn/automata-archive#45).
- **Breaking:** runs are a builder, `Deterministic::run(word)` / `run_from(state, word)` returning `ts::run::Run` (leonbohn/automata-archive#47). Whether the word is finite or infinite is chosen by its type, via the new associated type `Word::Kind` (`word::Finite` or `word::Omega`, implied by `FiniteWord` and `OmegaWord`). `Run` is executed with `observe::<O>()`, `evaluate::<O>()`, `escape_prefix()`, `is_successful()` and, for finite words, `reached_state()`, `reached_state_color()` and `last_edge_color()`. The 24 run helpers of `Deterministic` are removed, only `reached_state(word)` and `reached_state_from(state, word)` remain (they replace `reached_state_index` and `reached_state_index_from`). A run on an omega word iterates `OmegaWord::spoke` and `cycle` instead of calling `Word::nth`, does not collect the spoke and the cycle, finds the loop with a `StateMap` over the states at the ends of the passes through the cycle and observes each pass once, with its own observer; the observers of the passes in the loop are combined with the new required method `Observer::merge`. There is no `BTreeMap` and no `finite_run_from` per loop iteration, and a run without an observer (`NoObserver`, `escape_prefix`, `is_successful`) keeps nothing per pass. `Observer` loses `current` and gains `merge`; `InfiniteObserver` and `loop_back` are gone (every observer works on omega words) and `FiniteRunOutput`, `InfiniteRunOutput`, `RunResult` are replaced by `RunOutput` and `EscapePrefix` (the escape state is no longer part of the result; it is `reached_state` of the prefix). The observers `StateSequence`, `StateColorSequence` and `StateColorSet` are removed. Migration for `automata-learning`:
  - `ts.omega_run::<_, NoObserver>(w).is_escaping()` is `!ts.run(w).is_successful()`
  - `ts.omega_run::<_, Triggers<_>>(w)` is `ts.run(w).evaluate::<Triggers<_>>()`, with `RunOutput::Reached` and `RunOutput::Escaped(prefix)` instead of `InfiniteRunOutput::Successful` and `Failed(state, prefix)`
  - `ts.omega_escape_prefix(w)` is `ts.run(w).escape_prefix()`
  - `ts.omega_escape_prefixes(words)` is `words.filter_map(|w| ts.run(w).escape_prefix()).unique()`
  - `reached_state_index(_from)` is `reached_state(_from)`
  - `reached_state_color(_from)` is `ts.run(w).reached_state_color()` (`ts.run_from(q, w)` from a state)
  - `last_edge_color(_from)` is `ts.run(w).last_edge_color()`
  - `recurrent_edge_colors(w)` is `ts.run(w).observe::<EdgeColorSet<_>>()`, `recurrent_state_indices(w)` is `observe::<StateSet<_>>()`
  - `visited_edge_colors(w)` is `ts.run(w).observe::<EdgeColorSequence<_>>()`
- **Breaking:** `TransitionSystem::maybe_initial_state` (use `Dottable::dot_initial_state`), `hint_size` (it was never overridden; use `state_bound`), `make_expression` (use `alphabet().make_expression`), `edges_matching`, `all_accepting_dfa` (use `map_state_colors(|_| true)`), `is_reachable`, `reachable_states`, `reachable_states_from` and `reachable_state_colors` (use `reachable_state_indices*`, which return the same `Bfs`), and `IntoTs for MatchingProduct` (leonbohn/automata-archive#44).
- **Breaking:** `Dottable::try_open_svg_in_firefox`, use `display_rendered` or `display_rendered_graphviz`.
- **Breaking:** the trait `Show` (and `show`, `show_collection`) is removed; use `Display`. This includes the `Show` impls for `Path`, `Lasso`, `RunProfile`, `ProductIndex`, `Class`, `PeriodicOmegaWord`, `ReducedOmegaWord`, tuples, `Vec` and primitive types.
- Unused dependencies `bimap`, `tabled`, `owo-colors` and `rand_distr`.

[Unreleased]: https://github.com/leonbohn/automata/compare/v0.2.1...HEAD
[0.2.1]: https://github.com/leonbohn/automata/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/leonbohn/automata/compare/v0.1.0...v0.2.0
