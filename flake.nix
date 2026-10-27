{
  description = "automata: benchmark tracking (runner, dashboard, webhook service) and development shell";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

  outputs =
    { self, nixpkgs }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system nixpkgs.legacyPackages.${system});
    in
    {
      packages = forAllSystems (
        system: pkgs: rec {
          # The benchmark runner. It carries the toolchain that builds and benchmarks every
          # revision, so all commits are measured with the same compiler.
          automata-bench = pkgs.callPackage ./nix/package.nix { };
          default = automata-bench;
        }
      );

      # `nix run .#bench -- compare --base main` compares the current checkout against `main`
      # on this machine, exactly as the service does for pull requests.
      apps = forAllSystems (
        system: pkgs: {
          bench = {
            type = "app";
            program = "${self.packages.${system}.automata-bench}/bin/automata-bench";
          };
          default = self.apps.${system}.bench;
        }
      );

      # Import this on the machine that runs the benchmarks.
      nixosModules.default = import ./nix/module.nix self;

      devShells = forAllSystems (
        system: pkgs: {
          default = pkgs.mkShell {
            packages = [
              pkgs.cargo
              pkgs.rustc
              pkgs.clippy
              pkgs.rustfmt
              pkgs.cargo-hack
              self.packages.${system}.automata-bench
            ];
          };
        }
      );

      checks = forAllSystems (
        system: pkgs: {
          # builds the runner and runs its unit tests
          automata-bench = self.packages.${system}.automata-bench;

          # the module evaluates and produces a sensible unit
          nixos-module =
            let
              eval = nixpkgs.lib.nixosSystem {
                inherit system;
                modules = [
                  self.nixosModules.default
                  {
                    services.automata-bench = {
                      enable = true;
                      webhookSecretFile = "/run/secrets/webhook";
                      githubTokenFile = "/run/secrets/token";
                      virtualHost = "bench.example.org";
                      cpu = "1";
                    };
                    system.stateVersion = "25.11";
                    boot.loader.grub.enable = false;
                    fileSystems."/" = {
                      device = "none";
                      fsType = "tmpfs";
                    };
                  }
                ];
              };
              unit = eval.config.systemd.services.automata-bench;
            in
            pkgs.writeText "automata-bench-unit" ''
              ${unit.serviceConfig.ExecStart}
              ${builtins.toJSON eval.config.services.nginx.virtualHosts."bench.example.org".locations}
            '';
        }
      );

      formatter = forAllSystems (_: pkgs: pkgs.nixfmt);
    };
}
