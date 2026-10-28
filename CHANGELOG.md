# Changelog

All notable changes to this project are documented in this file.
The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html). While the version is 0.x, minor releases may contain breaking changes.

## [Unreleased]

### Added

- Rendering with an installed graphviz, mirroring the native backend: `Dottable::try_svg_graphviz`, `try_data_url_graphviz` and `render_graphviz` (PNG), next to the existing `try_svg`, `try_data_url` and `render` (features `graphviz` and `render`).
- `dot::open_in_viewer` and `dot::svg_to_data_url` as public helpers.
- `Dottable::dot_initial_state`: the initial state is marked in the DOT output by an arrow without source (an `init` node with an edge into the initial state). Implemented for DFAs, right congruences, Moore and Mealy machines and DPAs.
- `RenderError::DotNotFound` and `RenderError::DotFailed { status, stderr }` for problems with the `dot` executable.
- `examples/dot.rs` takes `--show` and `--show-graphviz` to open the rendered automaton in a viewer.
- Deterministic benchmarks that count instructions with gungraun (`scc`, `ts`, `runs`, `dfa`, `dpa`; `cargo bench`, needs valgrind) on closed-form inputs and on 22 DPAs generated with Spot (`benches/fixtures`, `scripts/generate_benchmark_fixtures.sh`), and a criterion target for wall-clock times. There is no randomness in the benchmarks.
- Benchmark tracking (see `docs/benchmarking.md`): `tools/bench` runs and compares the benchmarks (one execution per revision, 2 % threshold on instruction counts), a Nix flake provides it and a NixOS module that benchmarks `main` and pull requests labelled `performance` on a dedicated machine.
- README: table of the rendering functions, a recommendation of `graphviz`, and the prerequisites; crates.io and docs.rs badges.

### Changed

- **Breaking:** `IndexType` and `ScalarIndexType` are replaced by `IdType` and `DenseId` (`from_usize`, `into_usize`, `into_id` instead of `into_index`), implemented for `u8`, `u16`, `u32` and `usize`. `IdType` is no longer implemented for every type: `ProductIndex` and custom ids need an (empty) `impl IdType`. Added the newtype `EdgeId(u32)` (#41).
- Added `TransitionSystem::state_bound`, overridden by the linked list and forwarded by the wrappers, and the id containers (hash based fallback uses `FxBuildHasher`) `StateSet`, `StateMap` and `CompactIdMap`, which use bitsets and vectors for dense ids and hash containers otherwise. They replace the B-tree and hash based visited sets in `Reachable`, `LengthLexicographicMinimalRepresentatives`, omega runs, the `run::StateSet` observer (now derefs to `ts::StateSet` instead of `BTreeSet`; iteration order is only sorted for dense ids), both Tarjan variants, Kosaraju and the Hopcroft style partition refinement (#41).
- The bitset dependency is `fixedbitset` instead of `bit-set`.
- **Breaking:** removed the type aliases `math::OrderedSet`, `math::OrderedMap` and `math::Bijection` and the reexports `math::ordered_set` and `math::ordered_map`; use `BTreeSet`, `BTreeMap`, `bimap::BiBTreeMap` and `std::collections::{btree_set, btree_map}` directly (#64).
- **Breaking:** `math::Set` and `math::Map` are renamed to `math::FxIndexSet` and `math::FxIndexMap` and use the deterministic `rustc_hash::FxBuildHasher` instead of a randomly seeded one, so iteration order and benchmark instruction counts are reproducible. They are created with `default()` instead of `new()`. The hash maps in the SCC and normalization code use the same hasher.
- **Breaking:** `math::Partition` moved to `partition::Partition`.
- `DPA::normalized` stores the recoloring in a `HashMap` instead of a linearly searched `Vec` and collects the transition system only once (#39).
- Removing edges and states of a `LinkedListTransitionSystem` (`remove_edges_from`, `remove_edges_to`, `remove_edges_between`, `remove_edges_from_matching`, `remove_edges_between_matching`, `remove_state`) walks the edge lists of the states involved instead of scanning all edges, so the cost is proportional to the degree. The order of the returned edges may differ.
- `IntoTs::into_dfa_with_initial` only requires `Deterministic<StateColor = bool>` instead of `Congruence`, since the initial state is given explicitly.
- **Breaking:** `display_rendered` and `display_rendered_graphviz` now write an SVG to a temporary file and open it with the default program of the system (`xdg-open` on Linux, `open` on macOS, `start` on Windows) instead of piping a PNG to ImageMagick's `display`. This works on Wayland. The `IMAGE_VIEWER` environment variable is still honored, the program is now called with the path of the file instead of reading from stdin. The temporary file is not deleted.
- **Breaking:** the `graphviz` feature no longer implies `render`; it does not pull in `layout-rs`, `resvg` and `usvg` anymore.
- **Breaking:** `RenderError` is `#[non_exhaustive]`, `PngDisplayError` was renamed to `Io` and `NonZeroExit` was replaced by `DotFailed`. Variants that belong to the native backend only exist with the feature `render`.
- `render_to_file_name` (feature `graphviz`) takes the output format from the file extension (default `png`) and no longer uses a temporary file.
- Data URLs are encoded with padded base64 and keep the XML prolog of the SVG.
- `src/dot.rs` was split into the module `dot` (`attributes`, `impls`, `native`, `graphviz`, `render`); the public paths are unchanged.

- Dependencies: `rand` 0.8 to 0.10 (the `random` module uses `rand::rng()` and `RngExt`) and `tabled` 0.16 to 0.22. No public signatures change; the output of the transition tables is unchanged.

### Removed

- **Breaking:** `Dottable::try_open_svg_in_firefox`, use `display_rendered` or `display_rendered_graphviz`.

[Unreleased]: https://github.com/leonbohn/automata/compare/v0.1.0...HEAD
