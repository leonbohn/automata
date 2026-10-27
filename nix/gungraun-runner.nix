# The runner that gungraun calls. Its version must match the `gungraun` dependency in Cargo.toml
# (which is pinned with `=`), so update both together.
{ lib, rustPlatform, fetchCrate }:

rustPlatform.buildRustPackage rec {
  pname = "gungraun-runner";
  version = "0.20.0";

  src = fetchCrate {
    inherit pname version;
    hash = "sha256-XZHnq0t5XI/lSAdtP0UYxcaaV/YVZOmT/E7YQWX7jOU=";
  };
  cargoHash = "sha256-nYOFsVAuLw13XObUO4mS4edlv5N/BSHRYPPS1N7y0Os=";

  # its tests run valgrind and perf, which do not work in the build sandbox
  doCheck = false;

  meta = {
    description = "Runner for gungraun, valgrind based benchmarks for Rust";
    homepage = "https://github.com/gungraun/gungraun";
    license = with lib.licenses; [ asl20 mit ];
    mainProgram = "gungraun-runner";
  };
}
