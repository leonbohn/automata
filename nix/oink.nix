# Oink (https://github.com/trolando/oink), a collection of parity game solvers. Used as the
# reference solver for the differential tests and the benchmark comparison of `automata::game`.
# (The package called `oink` in nixpkgs is an unrelated DDNS updater.)
{
  stdenv,
  lib,
  fetchFromGitHub,
  cmake,
  boost,
}:
let
  # oink fetches lace with FetchContent, which does not work in the sandbox
  lace = fetchFromGitHub {
    owner = "trolando";
    repo = "lace";
    rev = "v2.3.2";
    hash = "sha256-LFXKq4I++ld+KgBPj0GitMtP41hU0BZohditwQ+F3T8=";
  };
in
stdenv.mkDerivation {
  pname = "oink-parity";
  version = "unstable-2026-06-03";

  src = fetchFromGitHub {
    owner = "trolando";
    repo = "oink";
    rev = "8fbf0a7c3e5b0baa254cb4516258c5c42fa99db1";
    hash = "sha256-t1trjV1UcVID+KwivTsU4S/TghurNwJcM5BD5gZs5k4=";
  };

  nativeBuildInputs = [ cmake ];
  buildInputs = [ boost ];

  cmakeFlags = [
    "-DFETCHCONTENT_SOURCE_DIR_LACE=${lace}"
    "-DFETCHCONTENT_FULLY_DISCONNECTED=ON"
    # reproducible binaries instead of -march=native
    "-DOINK_BUILD_NATIVE=OFF"
    "-DOINK_BUILD_TESTS=OFF"
  ];

  # the build does not install the tools
  installPhase = ''
    runHook preInstall
    mkdir -p $out/bin
    install -m755 oink $out/bin/
    runHook postInstall
  '';

  meta = {
    description = "Implementations of modern parity game solvers";
    homepage = "https://github.com/trolando/oink";
    license = lib.licenses.asl20;
    mainProgram = "oink";
  };
}
