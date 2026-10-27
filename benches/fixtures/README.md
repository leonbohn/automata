# Benchmark fixtures

Deterministic parity automata (DPAs) in the HOA format that the benchmarks read. They are
**generated with [Spot](https://spot.lre.epita.fr) (version 2.14.5)**; none of this would exist
without it. The files are committed so that benchmarks neither need Spot nor depend on
random numbers. Regenerate them with `scripts/generate_benchmark_fixtures.sh`, which needs the
Spot tools `genltl`, `ltl2tgba`, `randaut`, `genaut` and `autfilt`. Regenerating changes the
benchmark inputs, so it invalidates the history of the benchmarks.

Every fixture is deterministic, complete, colored (exactly one priority per edge), uses
`parity min even`, has one initial state and no unreachable states
(`autfilt --deterministic --complete --colored-parity='min even' --remove-unreachable-states`).

| Directory | How it was obtained | Files | States |
|---|---|---|---|
| `ltl/` | Formulas from `genltl` (parametrised families for n = 1 to 3 and the first four larger automata of each pattern collection), translated with `ltl2tgba --deterministic --generic`, then converted with `autfilt` | 53 | 2 to 152 |
| `random/` | `randaut --deterministic --colored --acceptance='parity min even P'` with fixed seeds, non-empty languages only. The seed is part of the file name. | 13 | 16 to 256 |
| `hard/` | `genaut --m-nba`, `--l-nba`, `--ks-nca`, `--l-dsa` for n = 2 and 3, converted to parity with `autfilt`. These force many states and priorities. | 8 | 7 to 726 |

File names say what they are: `ltl/gh-r-2.hoa` is `genltl --gh-r=2`,
`random/n64-a2-p4-s1.hoa` has 64 states, 2 atomic propositions, 4 priorities and seed 1. The
`name:` header of each file repeats this. Automata with more than 200 states, or that Spot
needs more than 10 seconds or 1 GB to produce, are left out on purpose: the benchmarks run
under valgrind, which is slow.

References for the formula families are in `genltl --help` and the Spot documentation.
