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
    ];
  };
  cargoLock.lockFile = ../tools/bench/Cargo.lock;

  nativeBuildInputs = [ makeWrapper ];

  postInstall = ''
    wrapProgram $out/bin/automata-bench --prefix PATH : ${
      lib.makeBinPath [
        cargo
        rustc
        gcc
        git
        util-linux # taskset
        coreutils
      ]
    }
  '';

  meta = {
    description = "Benchmark runner, history database, dashboard and webhook service for the automata crate";
    mainProgram = "automata-bench";
    license = lib.licenses.mit;
  };
}
