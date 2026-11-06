# Spot (https://spot.lre.epita.fr) with its Python bindings (`import spot`) and command line tools.
{
  stdenv,
  lib,
  python3,
  fetchurl,
}:
stdenv.mkDerivation rec {
  pname = "spot-platform";
  version = "2.16.2";

  src = fetchurl {
    url = "http://www.lre.epita.fr/dload/spot/spot-${version}.tar.gz";
    hash = "sha256-UvjQbPm/GuG0MJ7F00Ge9071wZm3HHCiNS5MTwojAqw=";
  };

  nativeBuildInputs = [ python3 ];
  buildInputs = [ python3 ];

  configureFlags = [
    "--disable-devel"
    "--disable-doxygen"
    "--enable-c++20"
  ];

  enableParallelBuilding = true;
  # the test suite takes very long
  doCheck = false;

  # lets `python3.withPackages (ps: [ spot-platform ])` find the bindings
  passthru.pythonModule = python3;

  meta = {
    description = "C++/Python LTL and ω-automata manipulation library and tools";
    homepage = "https://spot.lre.epita.fr/";
    license = lib.licenses.gpl3Plus;
    platforms = lib.platforms.unix;
  };
}
