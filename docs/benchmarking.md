# Benchmarking

Wall-clock times of a benchmark depend on the machine, on what else it is doing and on the number of
rounds, so changes of a few percent drown in noise. The benchmarks of this repository therefore count
**instructions** instead. They run under [valgrind](https://valgrind.org) with
[gungraun](https://github.com/gungraun/gungraun) (the successor of `iai-callgrind`), once, and give the
same numbers every time: repeated runs differ by a small fraction of a percent, so any difference larger
than that is a change of the code.

There are three layers:

1. **Benchmarks** in `benches/`: deterministic inputs, operations that are used in practice.
2. **`automata-bench`** (`tools/bench`): runs the benchmarks of one revision, or of two revisions to
   compare them.
3. **A service** (`automata-bench serve`, NixOS module in `flake.nix`) that does this on a dedicated
   machine for every commit on `main` and for pull requests labelled `performance`, keeps the history in
   SQLite and serves a dashboard.

## The benchmarks

| Target | Content |
|---|---|
| `scc` | Strongly connected components (iterative and recursive Tarjan, Kosaraju) on rings, paths, trees, grids, chains of cycles, irregular graphs |
| `ts` | Building a transition system edge by edge and with the builder, edge lookup, products, reachability, minimal representatives, predecessors, `clone`/`collect`/`map_edge_colors`, removing edges and states, subset construction |
| `runs` | Runs of finite words (one long word, many short ones), runs of lassos, infinity sets (recurrent edge colors and states), visited sequences, on synthetic and on fixture automata |
| `dfa` | Minimization (Hopcroft/Moore, with and without edge colors), union, intersection, complement, emptiness and witness, equivalence |
| `dpa` | Normalization, complement, accepted/rejected words, witnesses per priority, equivalence/inclusion/counterexamples, SCCs, prefix partition, HOA parsing and printing |
| `wallclock` | A handful of the same operations with criterion, see below |

Operations that do not exist yet (for example union and intersection of DPAs, or complementation of NFAs)
have no benchmark; each PR that adds one adds its benchmark to the same inputs.

**No randomness.** Inputs are pure functions of their size (`benches/common`): rings, counters,
affine maps modulo `n` for irregular but fixed structure, Thue-Morse words. The automata read from files
are the committed fixtures in `benches/fixtures` (HOA, generated once with
[Spot](https://spot.lre.epita.fr), see its README and `scripts/generate_benchmark_fixtures.sh`).
Because parsing HOA is slow, and every benchmark runs in its own process, the fixture benchmarks use
fixed selections of these files (`LTL` and `SYNTHETIC` in `benches/common/mod.rs`).

**What is measured.** Gungraun measures the benchmark function only; the `setup` function of a benchmark
(generating or parsing the input) is not counted, although it runs under valgrind and takes time. A
benchmark that finishes in a few thousand instructions did not do anything: the tool warns about those.
Benchmarks that stop at the first state (a witness found immediately, a refutation in the initial state)
are avoided on purpose, the inputs are built so that the search has to do its work.

**Memory.** For `scc`, `ts`, `dfa` and most of `runs` the benchmarks also run under DHAT, which counts
the bytes and the number of heap allocations. This roughly doubles the time of these benchmarks, so it is
off for the fixture benchmarks and for `dpa`. Add `config = LibraryBenchmarkConfig::default().tool(Dhat::default())`
to a benchmark (or to `main!`) to enable it.

**Wall-clock times.** `benches/wallclock.rs` uses criterion on a few operations, for real magnitudes.
They are only shown in the detail view of a run and never compared or graphed.

## Locally

You need `valgrind` and the `gungraun-runner` whose version equals the pinned `gungraun` dependency
(`cargo install gungraun-runner --version 0.20.0 --locked`, or `nix develop`).

```shell
cargo bench --bench scc                                    # one target
cargo bench --bench dpa -- '*::normalized::*'              # filter by module path
nix run .#bench -- run --rev HEAD                          # the whole suite, as a table
nix run .#bench -- compare --base main                     # your checkout against main
nix run .#bench -- check-determinism --runs 3              # run the suite again and compare the counts
```

Without Nix, `cargo run --manifest-path tools/bench/Cargo.toml -- compare --base main` does the same with
your own toolchain. Both revisions are checked out into worktrees (under `.git/automata-bench`) and built
once; each is executed once. A revision uses *its own* `benches/`; benchmarks that exist only on one side
show up as `new` or `removed`. A change is reported if the instruction count differs by more than the
threshold (2 % by default) and by at least 1000 instructions.

The whole suite takes about 9 minutes on the development machine (build and wall-clock target included), most of it spent
parsing fixtures under valgrind.

### Adding a benchmark

```rust
// benches/ts.rs
fn input(n: usize) -> Dts { common::scrambled(n, 2) }   // setup, not measured

#[library_benchmark]
#[benches::scrambled(args = [1_000, 4_000], setup = input)]
fn my_operation(ts: Dts) -> usize {
    black_box(ts.sccs().size())        // measured; return something so the work is not optimized away
}
```

and list the function in the `library_benchmark_group!` of the file. Keep the input free of randomness,
check that the benchmark does real work (the instruction count should grow with the input), and keep a
single benchmark below a few seconds under valgrind.

## Pull requests

Label a pull request that is meant to change performance with `performance`. The service then

1. takes the measurement of the merge base from its history (every commit of `main` is measured), and
   benchmarks it only if it is missing,
2. benchmarks the head of the pull request once,
3. stores everything in its database, and
4. posts (and later edits) one comment with the comparison and sets a `benchmarks` commit status. The
   status reports the outcome (success, or error if the run failed) and never blocks a
   merge on its own.

Pushing to a labelled pull request runs it again; removing the label or closing the pull request
cancels queued runs. Every commit of a push to `main` is benchmarked, oldest first, which gives one point
per commit in the history.

### Trust

The service compiles and runs the code of the pull request. It therefore only starts a run if the label
was applied by a user in `allowedLabelers` (by default the owner of the repository), later pushes to an
already labelled pull request inherit that trust, and pull requests from forks are skipped unless
`allowForks` is set. The unit is sandboxed (own user, read-only system, no capabilities, no access to
`/home`), but it has network access, since cargo downloads dependencies. Review the diff of a pull
request before labelling it, and re-check after the author pushes.

## The dashboard

Plain HTML and CSS, server-rendered, with inline SVG charts. The only JavaScript library is
[htmx](https://htmx.org) (version 4, vendored in `tools/bench/static`, no request leaves the site) which
swaps the queue and the history without reloading. The page has no script of its own.

- **History of `main`**: a stacked chart of the whole suite (per benchmark file, or per benchmark of one
  file) and one chart per benchmark, one point per commit. The metric can be switched between instructions,
  estimated cycles, allocated bytes and allocations. Points that changed by more than the threshold are red
  or green.
- **Pull requests** and the **detail view of a run**: the comparison, the environment, the log (live while
  the run is going), and the wall-clock times.
- **Queue**: the running and the waiting runs, refreshed every few seconds.

The dashboard is read-only: apart from the signed webhook, no request changes anything, so there is
no login and no token. Removing the label or closing the pull request drops its queued runs; a run that
is already going finishes (stop the service to end it, it is queued again on the next start).

`/data.json` has the instruction counts of the history.

## Setting up the machine

In the NixOS configuration of the benchmark machine:

```nix
{
  inputs.automata.url = "github:leonbohn/automata";
  # ...
  modules = [
    automata.nixosModules.default
    {
      services.automata-bench = {
        enable = true;
        virtualHost = "bench.example.org";            # nginx + ACME in front of the service
        webhookSecretFile = config.sops.secrets.bench-webhook.path;
        githubTokenFile = config.sops.secrets.bench-github-token.path;
        cpu = "1";                                    # pin to a CPU nothing else uses
      };
    }
  ];
}
```

Then, on GitHub:

- **Webhook** (repository settings): payload URL `https://bench.example.org/webhook`, content type
  `application/json`, the secret from `webhookSecretFile`, events *Pushes* and *Pull requests*.
- **Token** for `githubTokenFile`: fine-grained, only this repository, permissions *Pull requests: write*
  and *Commit statuses: write*.

State lives in `/var/lib/automata-bench`: `bench.sqlite` (history), `mirror.git` (the repository),
`work/` (worktrees and cargo target directories, so dependencies are built once), `logs/` (one file per
run). Databases written by the criterion based version keep their old numbers in the table
`legacy_criterion_results`; they are not shown.

The package and the development shell contain `valgrind` and the `gungraun-runner` matching the
`gungraun` version of `Cargo.toml` (`nix/gungraun-runner.nix`); change both together.

## Reading the numbers

- The instruction count is the number that decides. `Ir` includes everything the function and its callees
  execute, including allocation and memcpy, and counts every loop iteration, so it ranks algorithms by
  work and not by luck. It does not see cache effects; estimated cycles add a simple model of them, and
  the hit counts are in the detail view.
- Numbers from different compilers, targets or valgrind versions are not comparable. The history records
  the toolchain; do not mix.
- Counts are not bit-identical between runs, but nearly: most benchmarks differ by a few hundredths of a
  percent (address space layout, kernel). The library uses a fixed hasher (`rustc_hash::FxBuildHasher`,
  see `math::FxIndexMap`) instead of the randomly seeded `RandomState`, so hashing no longer contributes;
  the 2 % threshold predates this and is kept. `check-determinism` lists the benchmarks that vary most
  (default tolerance 2 %).
- Regenerating the fixtures changes the inputs of the fixture benchmarks and therefore breaks the
  history for those; mention it in the changelog.
