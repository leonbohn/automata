# versus: `automata` against Spot and Oink

Wall-clock comparison, see `docs/benchmarking.md`. Run it with the Python bindings built in release mode
(`maturin develop --release` in `python/`) inside `nix develop`:

```shell
python3 benches/versus/compare.py --list                    # the comparisons
python3 benches/versus/compare.py --filter game/ --out v.json
```

## Layout

- `compare.py`: the harness (`Case`, `Contender`, `@operation`, timing, JSON). The JSON is read by
  `tools/bench` (`model::Versus`): `settings` (tool versions, flags) and `rows` (`bench`, `reference`,
  `ours_ns`, `ref_ns`, sizes, `equivalent`, `runs`).
- `ops_automata.py`: DPA equivalence and inclusion against Spot on the fixtures.
- `ops_games.py`: parity games against Spot and Oink (`zlk`, `ppp`).

## Adding an operation

An operation is a generator of `Case`s. Everything done in the generator or before `run()` is not timed.

```python
@operation("dpa/determinize")                       # prefix of the benchmark name
def determinize(ctx):
    for name, s, a in inputs(ctx):                  # one case per input
        yield Case(
            name,
            ours=Contender(lambda a=a: a.determinize(), size=lambda r: r.num_states),
            refs={"spot": Contender(lambda s=s: spot.postprocess(s, "deterministic", "parity"),
                                    size=lambda r: r.num_states())},
            agree=lambda ours, theirs: ...,           # default: ==; compare languages for automata
        )
```

then `import` the module in `compare.py` (`main`) if it is new. A reference may be several tools
(`refs` has one entry per tool). Record settings that influence results (`postprocess` level, number of
workers) in `ctx.settings`. Keep one call above roughly a millisecond, and note that Spot has at most 32
acceptance sets. Benchmark names are tracked over time; rename them only deliberately.
