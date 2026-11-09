# Tests

```shell
cd python
python -m venv .venv && . .venv/bin/activate
pip install maturin pytest
maturin develop
python -m pytest                 # everything; the Spot tests are skipped if `import spot` fails
python -m pytest -m 'not spot'   # without the differential tests
python -m pytest -m spot         # only the differential tests (about 25 seconds)
```

The unit tests (`test_*.py` without `spot`) only need the extension. The differential tests against
[Spot](https://spot.lre.epita.fr) (`test_spot_*.py`, marker `spot`) need Spot's Python bindings and
its command line tool `randaut`; the repository's flake provides both: run `nix develop` first, then
the commands above inside the dev shell (`PYTHONPATH` makes `import spot` work in the venv). Without
Spot a `test_spot_*.py` module is skipped as a whole. CI runs them in the workflow
`.github/workflows/python-spot.yml` (weekly, on demand and for pull requests that touch the
automata code or the bindings).

## Differential tests

Spot's HOA goes into ours with `automata.parse_hoa(spot_aut.to_str("hoa", "t"))`, ours into Spot's
with `spot.automaton(aut.to_hoa())` (see `spot_helpers.py`). Words are ultimately periodic
(`OmegaWord`) and are handed to Spot as `prefix; cycle{period}`; Spot's answer for a word is whether
the automaton intersects the word. A failing assertion prints the HOA of every automaton involved.

| module | checks |
| --- | --- |
| `test_spot_roundtrip.py` | Spot HOA -> `parse_hoa` -> `to_hoa` -> Spot is equivalent (`spot.are_equivalent`); `parse_hoa` returns the expected class (DBA, DCA, DPA of all four kinds, DRA, DSA, NBA, NCA, NPA); the unsupported ones raise `NotImplementedError` |
| `test_spot_emptiness.py` | `is_empty` agrees with Spot, `accepting_word()` is accepted by Spot, `accepts` agrees with Spot on random lassos |
| `test_spot_inclusion.py` | `included_in`, `equivalent_to` and their counterexamples for `DBA`/`DPA` against `spot.contains`/`spot.are_equivalent`; a counterexample must be accepted by exactly one side (inclusion: by the left one only) |
| `test_spot_complement.py` | `complement()` is equivalent to `spot.dualize`, disjoint from the original and opposite on lassos; automata without a `complement` yet are skipped |
| `test_spot_conversions.py` | `from_dba`, `from_dca`, `from_dpa`, `to_min_even`, `normalized`, `streamlined` are equivalent to the source; `rejected_word` against the emptiness of Spot's dual |
| `test_spot_constructed.py` | automata built with our constructors (all classes, random), written by `to_hoa()`, agree with Spot on emptiness and lassos |
| `test_finite_words.py` | (no Spot) `DFA.minimize` against Moore partition refinement, `NFA.determinize` against brute force up to length 7 |

Inputs are the fixtures `benches/fixtures/**/*.hoa` and random automata of `randaut` with fixed
seeds (several acceptance conditions, deterministic and not, different densities).

Known bugs are marked `xfail(strict=True)` with the reason, so that fixing one makes the test fail
until the marker is removed. Inputs are normalized so that the other checks stay meaningful: HOA is
written with transition-based acceptance (`to_str("hoa", "t")`), edges are split into valuations
(`spot.split_edges`) for the inclusion tests, and `randaut --colored` gives every parity edge a
color.

## Adding inputs

* A new fixture file in `benches/fixtures` is picked up by every `fixture_*` test.
* More random automata: widen the `seeds`/`SEEDS` of the test or add an entry to `KINDS` in
  `spot_helpers.py` (acceptance string for `randaut`, class of `parse_hoa` for the deterministic and
  the nondeterministic case).
* A new check: write a function over `(spot automaton, our automaton)` pairs and parametrize it with
  `cases(KINDS)` (random automata) and `fixture_cases()` (fixtures); `lassos(num_aps, seed)` gives
  words, `spot_accepts` asks Spot, `msg` formats a failure with the HOA of the inputs.
