#!/usr/bin/env python3
"""Wall-clock comparison of `automata` with Spot and Oink ("versus").

    python3 benches/versus/compare.py --out versus.json [--filter dpa/] [--list]

Needs the Python bindings (`import automata`, `maturin develop` in `python/`) and Spot
(`import spot`); games are also solved with `oink` if it is on the PATH (or `$OINK`). Numbers are
the median of repeated calls. Parsing and building the inputs is never timed, and every
contender produces its full result inside the timed call. Each comparison also records whether
both sides computed the same thing (`equivalent`).

An operation is a function in `ops_*.py` that yields `Case`s, registered with `@operation`
(see `ops_automata.py`; `README.md` has a walk-through). The JSON is read by `tools/bench`.
"""

import argparse
import dataclasses
import json
import platform
import statistics
import sys
import time
from typing import Any, Callable, Iterable, Optional

OPERATIONS: dict[str, Callable[["Context"], Iterable["Case"]]] = {}


def operation(name: str):
    """Registers a generator of cases; `name` (e.g. `dpa/equivalence`) prefixes every case."""

    def register(f):
        OPERATIONS[name] = f
        return f

    return register


@dataclasses.dataclass
class Contender:
    """One side of a comparison.

    `run()` is the timed call and returns the result, or `(result, seconds)` if the tool measures
    itself (Oink runs as a process, so its start-up and parsing are not part of its time).
    `size` maps the result to a number comparable between the contenders (states, vertices).
    """

    run: Callable[[], Any]
    size: Callable[[Any], Optional[int]] = lambda result: None


@dataclasses.dataclass
class Case:
    """`name` is the input (e.g. `ltl/gh-r-3`), `refs` maps the reference's name to its contender
    and `agree(ours, theirs)` says whether two results are the same."""

    name: str
    ours: Contender
    refs: dict[str, Contender]
    agree: Callable[[Any, Any], bool] = lambda a, b: a == b


@dataclasses.dataclass
class Context:
    """What `ops_*.py` need from the environment; also collects what to record about it."""

    root: Any  # pathlib.Path of the repository
    settings: dict[str, Any] = dataclasses.field(default_factory=dict)


def measure(c: Contender, budget: float, min_runs: int, max_runs: int):
    """Median time in ns, the last result and the number of calls. Calls are repeated until
    `budget` seconds are used (but at least `min_runs` and at most `max_runs` times)."""
    times, result, start = [], None, time.perf_counter()
    while len(times) < min_runs or (
        time.perf_counter() - start < budget and len(times) < max_runs
    ):
        t0 = time.perf_counter_ns()
        out = c.run()
        t1 = time.perf_counter_ns()
        if isinstance(out, tuple):
            result, seconds = out
            times.append(seconds * 1e9)
        else:
            result = out
            times.append(t1 - t0)
    return statistics.median(times), result, len(times)


def main() -> int:
    import pathlib

    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", help="write the JSON here (default: stdout)")
    ap.add_argument("--filter", action="append", default=[], help="only names containing this")
    ap.add_argument("--list", action="store_true", help="list the comparisons and exit")
    ap.add_argument("--budget", type=float, default=1.0, help="seconds per contender")
    ap.add_argument("--min-runs", type=int, default=1)
    ap.add_argument("--max-runs", type=int, default=50)
    args = ap.parse_args()

    here = pathlib.Path(__file__).resolve().parent
    sys.path.insert(0, str(here))
    sys.modules.setdefault("compare", sys.modules[__name__])  # `ops_*` import us as `compare`
    ctx = Context(root=here.parents[1])
    import ops_automata, ops_games  # noqa: F401,E401  (register the operations)

    rows = []
    for op_name, make_cases in OPERATIONS.items():
        for case in make_cases(ctx):
            bench = f"{op_name}/{case.name}"
            if args.filter and not any(f in bench for f in args.filter):
                continue
            if args.list:
                print(bench, *case.refs)
                continue
            ours_ns, ours_result, runs = measure(case.ours, args.budget, args.min_runs, args.max_runs)
            for ref_name, ref in case.refs.items():
                ref_ns, ref_result, ref_runs = measure(ref, args.budget, args.min_runs, args.max_runs)
                rows.append(
                    {
                        "bench": bench,
                        "reference": ref_name,
                        "ours_ns": ours_ns,
                        "ref_ns": ref_ns,
                        "ours_size": case.ours.size(ours_result),
                        "ref_size": ref.size(ref_result),
                        "equivalent": bool(case.agree(ours_result, ref_result)),
                        "runs": min(runs, ref_runs),
                    }
                )
                print(
                    f"{bench} vs {ref_name}: {ours_ns / 1e6:.3f} ms / {ref_ns / 1e6:.3f} ms"
                    f"{'' if rows[-1]['equivalent'] else '  RESULTS DIFFER'}",
                    file=sys.stderr,
                )
    if args.list:
        return 0

    import automata

    ctx.settings.update(
        python=platform.python_version(), automata=automata.version(), budget_s=args.budget
    )
    text = json.dumps({"settings": ctx.settings, "rows": rows}, indent=1)
    if args.out:
        pathlib.Path(args.out).write_text(text)
    else:
        print(text)
    # differences are recorded (and shown), they do not fail the run
    return 0


if __name__ == "__main__":
    sys.exit(main())
