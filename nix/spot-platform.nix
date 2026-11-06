# Spot (https://spot.lre.epita.fr) with its Python bindings (`import spot`) and command line tools.
{
  stdenv,
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
  ];

  enableParallelBuilding = true;
  # the test suite takes very long
  doCheck = false;

  # make `import spot` work for anything that has this package in its environment
  passthru.pythonPath = "${placeholder "out"}/${python3.sitePackages}";
}
