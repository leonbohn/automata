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
- Criterion benchmarks (`cargo bench`) for SCC decompositions on several graph shapes and for common operations (reachability, minimization, products, subset construction).
- README: table of the rendering functions, a recommendation of `graphviz`, and the prerequisites; crates.io and docs.rs badges.

### Changed

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
