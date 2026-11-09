{
  lib,
  rustPlatform,
  makeWrapper,
  cargo,
  rustc,
  gcc,
  git,
  util-linux,
  coreutils,
  valgrind,
  gungraun-runner,
  maturin,
  python3,
  spot-platform,
  oink,
}:

rustPlatform.buildRustPackage {
  pname = "automata-bench";
  version = "0.1.0";

  src = lib.fileset.toSource {
    root = ../tools/bench;
    fileset = lib.fileset.unions [
      ../tools/bench/Cargo.toml
      ../tools/bench/Cargo.lock
      ../tools/bench/src
      ../tools/bench/static
    ];
  };
  cargoLock.lockFile = ../tools/bench/Cargo.lock;

  nativeBuildInputs = [ makeWrapper ];

  postInstall = ''
    wrapProgram $out/bin/automata-bench --prefix PYTHONPATH : ${spot-platform}/${python3.sitePackages} --prefix PATH : ${
      lib.makeBinPath [
        cargo
        rustc
        gcc
        git
        util-linux # taskset
        coreutils
        valgrind # the benchmarks run under callgrind and DHAT
        gungraun-runner # must match the version of the gungraun dependency
        # `benches/versus/compare.py`: builds the Python bindings, compares with Spot and Oink
        maturin
        python3
        oink
      ]
    }
  '';

  meta = {
    description = "Benchmark runner (instruction counts), history database, dashboard and webhook service for the automata crate";
    mainProgram = "automata-bench";
    license = lib.licenses.mit;
  };
}
