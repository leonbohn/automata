# Benchmark fixtures

Deterministic parity automata (DPAs) in the HOA format that the benchmarks read. They are
**generated with [Spot](https://spot.lre.epita.fr) (version 2.14.5)**; none of this would exist
without it. The files are committed so that benchmarks neither need Spot nor depend on
random numbers. Regenerate them with `scripts/generate_benchmark_fixtures.sh`, which needs the
Spot tools `genltl`, `ltl2tgba`, `randaut`, `genaut` and `autfilt`. Regenerating changes the
benchmark inputs, so it invalidates the history of the benchmarks.

Every fixture is deterministic, complete, colored (exactly one priority per edge), uses
`parity min even`, has one initial state and no unreachable states
(`autfilt --deterministic --complete --colored-parity='min even' --remove-unreachable-states`),
priorities are on the edges (`--hoaf=t`), and every edge label is a conjunction that mentions all
atomic propositions (`--split-edges`).

Three limitations of the HOA reader shape the files, none of them of Spot: it accepts at most 6
atomic propositions (automata with more are left out), it does not accept edge labels with
disjunctions (hence `--split-edges`), and the parser rejects the informative properties
`stutter-sensitive`, `terminal`, `very-weak`, `weak` and `inherently-weak`, which are therefore
removed from the files by the script.

| Directory | How it was obtained | Files | States |
|---|---|---|---|
| `ltl/` | Formulas from `genltl` (parametrised families for n = 1 to 3 and the first four larger automata of each pattern collection), translated with `ltl2tgba --deterministic --generic`, then converted with `autfilt` | 15 | 2 to 25 |
| `random/` | `randaut --deterministic --colored --acceptance='parity min even P'` with fixed seeds, non-empty languages only. The seed is part of the file name. | 4 | 16 to 256 |
| `hard/` | `genaut --m-nba`, `--l-nba`, `--ks-nca`, `--l-dsa` for n = 2 and 3, converted to parity with `autfilt`. These force many states and priorities. | 3 | 29 to 121 |

File names say what they are: `ltl/gh-r-2.hoa` is `genltl --gh-r=2`,
`random/n64-a2-p4-s1.hoa` has 64 states, 2 atomic propositions, 4 priorities and seed 1. The
`name:` header of each file repeats this. Automata with more than 200 states, or that Spot
needs more than 10 seconds or 1 GB to produce, are left out on purpose: the benchmarks run
under valgrind, which is slow.

References for the formula families are in `genltl --help` and the Spot documentation.

## Which files are kept

The script generates a superset and then keeps only the files the benchmarks read (the lists `LTL`
and `SYNTHETIC` in `benches/common/mod.rs`, which must match the list in the script). Parsing HOA is
slow (about 45 µs per edge, and benchmarks run under valgrind, roughly 100 times slower), and every
benchmark parses its inputs again, so the selection is small and avoids automata with many atomic
propositions. `tests/benchmark_fixtures.rs` checks that all files can be read.
