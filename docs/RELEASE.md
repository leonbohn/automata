# Releasing a new version of `automata`

Checklist for a release `X.Y.Z` (examples use `0.2.0`). Pre-1.0 rule: minor releases (`0.Y.0`) may
contain breaking changes, patch releases (`0.Y.Z`) must be additive or fix bugs only. Tags are
`vX.Y.Z` (existing: `v0.1.0`). Releases are cut from `main`, via a PR, never from a feature branch.
Confer before committing, pushing, tagging or publishing; `cargo publish` cannot be undone (a
version can only be yanked, never overwritten).

## 0. Decide the version

- [ ] Look at `CHANGELOG.md` "Unreleased": anything prefixed **Breaking:** means a minor bump
      (0.x) / major bump (>= 1.0); only additions and fixes mean a patch bump (0.x).
- [ ] `cargo semver-checks` (if installed) against the last release to catch accidental breaks:
      `cargo semver-checks check-release --baseline-version 0.1.0` (with the features you
      care about, e.g. `--all-features`).
- [ ] Check open blockers: milestone / issues labelled for the release, items in `PLAN.md`
      Phase 6 (e.g. issue #15), the panic audit (issue #7) if it is a stated release goal.

## 1. Prepare a release branch

- [ ] `git switch main && git pull` and ensure the working tree is clean.
- [ ] `git switch -c release/0.2.0`.

## 2. Dependencies and compatibility

- [ ] `cargo update` is optional; if you do it, run everything again afterwards. Check outdated
      dependencies: `cargo outdated -R` (or `cargo upgrade --dry-run`).
- [ ] Sibling crates:
      - `hoars` and `biodivine-lib-bdd` must stay on the same `Bdd`-compatible major (see
        `CLAUDE.md`); both must be **published versions on crates.io**, no `git`/`path`
        dependencies (publishing fails otherwise). `grep -n 'git =\|path =' Cargo.toml`.
      - `hoars` must be released first if this release needs a new `hoars`.
- [ ] `cargo deny check` / `cargo audit` (if configured) for advisories and licenses.
- [ ] MSRV: `rust-version` in `Cargo.toml` is still correct. If a dependency bump raises it, raise
      it deliberately, update `CLAUDE.md`, the CI `msrv` job and the changelog (MSRV bumps are
      breaking-ish and noted under "Changed").
- [ ] No unwanted duplicate dependency versions: `cargo tree -d`.

## 3. Version bump and documents

- [ ] `Cargo.toml`: `version = "0.2.0"`.
- [ ] `CHANGELOG.md`:
      - rename `## [Unreleased]` to `## [0.2.0] - YYYY-MM-DD` and add a fresh empty
        `## [Unreleased]` above it;
      - make sure every user-visible change is listed under Added/Changed/Fixed/Removed, breaking
        ones prefixed **Breaking:**, big rewrites with migration tables;
      - add/update the compare links at the bottom, if the file uses them
        (`[0.2.0]: https://github.com/leonbohn/automata/compare/v0.1.0...v0.2.0`).
- [ ] `README.md`: install instructions say `cargo add automata` (and the current version if
      versions are shown); badges for crates.io / docs.rs / CI present; feature table matches
      `[features]` in `Cargo.toml` exactly.
- [ ] Crate docs (`#![doc = include_str!("../README.md")]`): the README doctests pass in all
      feature configurations.
- [ ] `CLAUDE.md` / `PLAN.md` / `PERFORMANCE.md`: tick finished items, remove stale statements
      (e.g. version number in "What this is", "heading for 0.2.0").
- [ ] Grep for the old version number in docs/examples: `grep -rn '0\.1\.0' --include=*.md --include=*.rs --include=*.toml . | grep -v target | grep -v CHANGELOG`.
- [ ] `Cargo.toml` metadata is complete: `description`, `license`, `repository`, `homepage`,
      `readme`, `keywords` (max 5), `categories`, `authors`, `rust-version`, `exclude`.
- [ ] Docs.rs build config, if needed: `[package.metadata.docs.rs] all-features = true`
      (so feature-gated items are documented). With `render`/`graphviz` this must not need system
      libraries or network access on docs.rs; check with the `docs` command in step 4.

## 4. Verify locally

Run everything CI runs, then the release-specific checks.

- [ ] `./scripts/check` (fmt, clippy in 3 configurations, docs with `-D warnings`,
      `cargo hack check --each-feature --no-dev-deps`, MSRV 1.88, tests in 3 configurations,
      examples, bench tooling). Make sure `cargo-hack` and the 1.88 toolchain are installed so
      nothing is silently skipped.
- [ ] `cargo bench --no-run` builds all benches; optionally run the benchmark suite once and
      compare with the previous release via `tools/bench` (`docs/benchmarking.md`) and note
      notable regressions/improvements in the changelog.
- [ ] `nix flake check` (CI has a `nix` job); update `flake.nix` version if it hard-codes one.
- [ ] Tests on a clean checkout, to catch files that only exist locally:
      `git stash -u` or `git clone . /tmp/release-check && cd /tmp/release-check && cargo test --all-features`.
- [ ] Docs as docs.rs will build them:
      `RUSTDOCFLAGS="--cfg docsrs -D warnings" cargo +nightly doc --no-deps --all-features`
      (drop `+nightly` / `--cfg docsrs` if the crate does not use `doc_cfg`).
- [ ] Packaging:
      - `cargo package --list` — inspect: no fixtures, secrets, large files, `target/`; confirm
        the `exclude` list works (`benches/fixtures`, `tools`, `docs`, `nix`, `.github`, ...).
        Note: `benches/` sources are included but `benches/fixtures` is excluded; the benches
        must not make `cargo package`'s verification build fail (it builds the library, and
        checks `[[bench]]` targets exist or are excluded consistently). If packaging complains,
        fix `exclude`/`[[bench]]` entries, don't remove checks.
      - `cargo package` (builds the tarball and compiles it in isolation);
      - `cargo publish --dry-run`.
- [ ] Check size: `ls -lh target/package/automata-0.2.0.crate` (crates.io limit is 10 MiB).

## 5. Release PR

- [ ] Commit (`Release 0.2.0`), push, open a PR `release/0.2.0` -> `main`.
- [ ] Wait for all CI jobs (fmt, clippy, docs, features, msrv, test, test-all-features, benches,
      bench-tools, nix).
- [ ] Review the diff of just the release commit: version, changelog, README, docs only.
- [ ] Merge (fast-forward/squash as per repo habit). Then
      `git switch main && git pull` and verify `HEAD` is the merged release commit.

## 6. Tag and publish

- [ ] Make sure you are on the merged `main` commit with a clean tree: `git status`, `git log -1`.
- [ ] Log in once if needed: `cargo login` (token with publish scope; do not paste the token in
      shell history or logs).
- [ ] `cargo publish --dry-run` once more on the final commit.
- [ ] `cargo publish`.
- [ ] Wait until the crate shows up: `cargo search automata`, <https://crates.io/crates/automata>.
- [ ] Tag the exact published commit and push the tag:
      `git tag -a v0.2.0 -m "automata 0.2.0"` then `git push origin v0.2.0`.
- [ ] Create the GitHub release from the tag; body = the changelog section for 0.2.0 (this is
      where the migration table belongs for breaking releases).
- [ ] Check <https://docs.rs/automata/0.2.0>: build succeeded, feature-gated items are visible,
      README renders, no broken links. If the build failed, fix and publish a patch release
      (docs.rs rebuilds are not automatic for the same version unless it is a docs-only
      infrastructure fix).

## 7. After the release

- [ ] Smoke test as a consumer in a throwaway directory (not inside this repo):
      ```shell
      mkdir /tmp/consumer && cd /tmp/consumer && cargo init
      cargo add automata@0.2.0        # also try --features hoa, and --no-default-features
      # paste the README quick start into src/main.rs
      cargo run
      ```
- [ ] Update downstream: `frieda` (`omega-learning-tasks` etc.) and `automata-learning` if still
      alive, per the migration notes in the changelog.
- [ ] Back on `main`: `CHANGELOG.md` has an empty "Unreleased"; optionally bump `Cargo.toml` to the
      next pre-release version (`0.3.0-dev`) if you want local builds distinguishable (don't
      publish it).
- [ ] Update `PLAN.md` (Phase 6 items) and close the milestone / release issue.
- [ ] Announce (if desired): GitHub release, relevant community channels; mention the
      `performance`-relevant numbers if the release is performance-driven.

## If something goes wrong

- **Bug found right after publishing:** `cargo yank --version 0.2.0` only stops *new* resolutions
  from picking it; it does not delete it. Fix on `main`, release `0.2.1` through this same
  checklist, then yank the broken version if it is dangerous (wrong results, data loss, security).
- **Publish failed halfway** (e.g. network): re-run `cargo publish`; if the version already
  exists on crates.io, do not retag, just continue at the "Tag" step.
- **Wrong tag pushed:** if nobody has consumed it, delete (`git push --delete origin vX.Y.Z`,
  `git tag -d vX.Y.Z`) and retag; if the crate has been published from a different commit,
  prefer a new patch release over rewriting history.
- **Dependency yanked / new advisory before publish:** update the dependency, re-run step 4,
  amend the release PR.

## Appendix: patch release (`0.Y.Z`, additive or fix only)

Same checklist, with these differences:

- Version bump is `0.Y.(Z+1)`; the changelog has no **Breaking:** entries (`cargo semver-checks`
  agrees).
- If `main` already contains breaking changes meant for the next minor, release the patch from a
  `release/0.Y` maintenance branch created from the previous tag
  (`git switch -c release/0.2 v0.2.0`), cherry-pick the fixes, and tag from there. Merge the
  changelog section back into `main`.

## Appendix: future automation (not set up yet)

PLAN.md mentions release-plz / cargo-release. Once adopted, steps 3, 5 and 6 become: merge the
generated release PR, and the workflow tags, publishes and creates the GitHub release. The manual
verification in step 4 should stay as a required CI job so that automation cannot publish an
unverified tree.
