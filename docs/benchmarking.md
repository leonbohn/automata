# Benchmarking

Numbers from a single machine say little without something to compare against. This repository therefore
has three layers:

1. **Criterion benchmarks** in `benches/`. They use deterministic generators (`benches/common`) and only
   public API. `baseline.rs` is the set from #32 (the problems P1 to P5 of #30), `scc.rs`, `operations.rs` and
   `dpa.rs` (parity automata) are broader suites.
2. **`automata-bench`** (`tools/bench`): measures *two revisions against each other, on the same machine,
   in alternating rounds*, and reports the difference.
3. **A service** (`automata-bench serve`, NixOS module in `flake.nix`) that does this on a dedicated machine
   for `main` and for pull requests labelled `performance`, keeps the history in SQLite, writes a static
   dashboard and comments the comparison on the pull request.

## Locally

```shell
cargo bench --bench baseline -- --quick        # a couple of minutes
nix run .#bench -- compare --base main         # your checkout against main, same report as on a PR
nix run .#bench -- run --rev HEAD              # just the numbers
```

Without Nix, `cargo run --manifest-path tools/bench/Cargo.toml -- compare --base main` does the same
with your own toolchain. Both revisions are checked out into separate worktrees (under
`.git/automata-bench`), built once, and then benchmarked in rounds `base head head base base head ...`,
so slow drift of the machine hits both. A revision uses *its own* `benches/`; benchmarks that exist only
on one side show up as `new` or `removed`.

A change is reported if it exceeds the threshold (10 % by default) **and** the measurements do not
overlap: the range of a benchmark spans the confidence intervals of all rounds. The headline number is
the median over the rounds of each round's mean.

Run it on a quiet machine. Numbers from different machines are not comparable; that is why the history
below is recorded on one machine only.

## Pull requests

Label a pull request that is meant to change performance with `performance`. The service then

1. builds the merge base with `main` and the head of the pull request,
2. benchmarks both in alternating rounds,
3. stores everything in its database, and
4. posts (and later edits) one comment with the comparison and sets a `benchmarks` commit status. The
   status reports the outcome (success, or error if the run failed) and never blocks a merge on its own.

Pushing to a labelled pull request runs it again; removing the label or closing the pull request
cancels queued runs. Every push to `main` is benchmarked as well, which gives the history on the dashboard.

### Trust

The service compiles and runs the code of the pull request. It therefore only starts a run if the label
was applied by a user in `allowedLabelers` (by default the owner of the repository), later pushes to an
already labelled pull request inherit that trust, and pull requests from forks are skipped unless
`allowForks` is set. The unit is sandboxed (own user, read-only system, no capabilities, no access to
`/home`), but it has network access, since cargo downloads dependencies. Review the diff of a pull
request before labelling it, and re-check after the author pushes.

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
        virtualHost = "bench.example.org";            # nginx + ACME, dashboard and /webhook
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
`work/` (worktrees and cargo target directories, so dependencies are built once), `www/` (dashboard).

The dashboard is a single static `index.html` (data embedded, no external requests, no JavaScript
dependencies); `data.json` next to it has the same data.

## Reading the numbers

Even a pinned core on a VPS is noisy. Running the identical code twice against each other gave
deviations of up to about 10 % per benchmark in `--quick` mode, which is why the default threshold is
10 % *and* non-overlapping ranges are required. For sub-millisecond benchmarks treat anything below
that as noise, and rerun (`--rounds 5`) if a result matters. The history of `main` has one measurement
per commit; compare neighbours with care, and prefer the pull request comparison, which measures both
sides in the same session.

## Not done yet

- Instruction counts (`iai-callgrind`, needs valgrind) as a deterministic second signal, as suggested in
  #26. The runner only parses criterion output so far.
- Benchmarks of `automata-learning`.
