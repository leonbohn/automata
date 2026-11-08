# Panic audit

Library code does not panic on input. Panics that remain encode invariants or are documented with
a `# Panics` section. This file lists them for the module `automata::learning` (issue #138,
phase 6 of `docs/INTEGRATE.md`); the audit of the rest of the crate is tracked in issue leonbohn/automata-archive#7.

## Converted to errors

Everything that a caller can trigger with a wrong input now returns a `LearningError`
(convertible into `automata::Error`) instead of panicking:

| item | was | now |
| ---- | --- | --- |
| `passive::dfa_rpni` | `unwrap` on the result of `dpainf`, `expect` per positive word | `Result` (`Threshold`, `Incomplete`) |
| `passive::dba_rpni` | `todo!()` | `Err(Error::NotYetImplemented)` |
| `passive::infer_precise_dpa`, `dpa_rpni` | `unwrap`/`expect` on the prefix congruence, the split and the FORC | `Result` |
| `OmegaSample::split`, `SplitOmegaSample::infer_forc` | `unwrap`/`expect`/assertions | `Result` |
| `dpainf::iteration_consistency_conflicts` | `unwrap`, `panic!` for an unknown class | `Result` (`Incomplete`) |
| `SetSample::insert` | `assert!` against contradicting classifications | `Result` (`ConflictingClassification`); `classify` returns `None` for such a word |
| `OmegaSample::try_from_read` | `expect` on I/O errors (and an inverted line filter that dropped the content) | `OmegaSampleParseError::Io` |
| `AnnotatedCongruence::canonic_coloring` | `unwrap`/`expect`/`unreachable!` | `Result` (`Incomplete`, `Priorities`) |
| `AnnotatedCongruence::build` | `unwrap` on states without a representative | such states are not idempotent |
| `ConsistencyCheck::consistent_automaton` | `assert!`/`panic!`/`unwrap` | `Result` (`Inconsistent`, `Priorities`); `sprout` forwards it as `SproutError::Learning` |
| `precise::build_precise_dpa_for` | `panic!` for 0 or more than 8 priorities | `Result` (`Priorities`) |
| `PreciseDPA::from(fwpm)` | `assert!`, `panic!`, `Vec::insert` out of range | `PreciseDPA::try_from(fwpm)` |
| `PreciseDPA::new` | indexing | `Result` (`Incomplete`) |
| `PreciseDPA::take_precise_transition`, `Deterministic::edge` | `expect` on incomplete systems | `Option` / `None` |
| `LStar::infer` | `panic!` on the iteration threshold, `assert!` on the counterexample, `unwrap` of `MAX_ITERATIONS` | `Result` (`IterationThreshold`, `InvalidCounterexample`); an unparsable `MAX_ITERATIONS` is ignored |
| `MealyOracle::new`, `MooreOracle::new` | panic on the first query if the machine is incomplete | `Result` (`IncompleteOracle`) |
| `SampleOracle` | `todo!()` | implemented |
| `ConflictRelation`, `PreciseDPA` (`Debug`), `SeparatesIdempotents` | `todo!()` | implemented |
| `ConsistencyCheck<A> for ()` | `unimplemented!()` | removed |

## Remaining

| where | what | why it is fine |
| ----- | ---- | -------------- |
| `active/lstar.rs` (`update_table`, `hypothesis`, `rows_to_promote`, `process_counterexample`, `output`) | `assert!`, `unwrap`, `expect`, `panic!` on the observation table | private functions, they check the invariants of the table (every row has an entry for every experiment, the table is closed, queries are asked once). L\* establishes them before the call |
| `active/hypothesis.rs` | `expect` in `output_from`, `panic!`/`assert!` in `give_transition_color` | `# Panics` sections; L\* only builds complete hypotheses and passes rows that match the experiments |
| `active/oracle.rs` (`MooreOracle`) | `expect` on the output of the machine | the machine is complete (checked in `new`) |
| `passive/precise.rs` (`initial`) | `expect` on the first state | the vector of states is never empty |
| `passive/sprout/consistency.rs` (`to_infinity_sets`) | `expect` on the state reached by an escape prefix | the prefix before the escape symbol has a run by definition |
| `prefixtree.rs` | `debug_assert!` | only called with the non-empty words of a sample |

`passive/sample/characterize.rs` (dead code, never compiled) was deleted; it stays in `automata-learning`.

## Python bindings (`python/`)

Python input must never reach a panic. The bindings validate before they call the crate, a Rust
panic that gets through would surface as `pyo3_runtime.PanicException`.

| entry point | crate function that can panic | guard |
| ----------- | ----------------------------- | ----- |
| `PropAlphabet(aps)` | `PropAlphabet::new` | uses `try_new` (`PropAlphabetError`) |
| symbols of `PropAlphabet` automata | `PropSymbol::from_bools` (too many booleans) | the length is checked against the number of propositions |
| symbols of `CharAlphabet` automata | `Alphabet::make_expression` (symbol not in the alphabet) | `CharAlphabet::contains` check, `ValueError` |
| `OmegaWord(prefix, period)` | `ReducedOmegaWord::ultimately_periodic` (empty period) | `ValueError` |
| constructors and builders | indexing by state, `add_edge` | every state is checked against `num_states` before |
| `union`, `intersection`, comparisons, `bisimilar` | products of automata over different alphabets | the alphabet sizes are compared, `ValueError` |
| `edges_from`, `is_accepting` | state lookups | `IndexError` for unknown states |
| `from_hoa`, `parse_hoa` of the parity classes | `AcceptanceMask::as_priority` (edge without exactly one acceptance set) | the priorities are validated first (`check_priorities`, `AcceptanceError`), `into_dpa` validates itself |
| `PropDRA.from_hoa`, `PropDSA.from_hoa` | none: the masks are numbered by the bindings | more than 256 different masks are a `HoaError`, every mask of an edge is in the index by construction |
| `to_min_even`, `is_empty`, `accepting_word` of the parity variants | `u8` overflow of the renumbered colors | computed in `usize` and checked against `255`, `ValueError` |
