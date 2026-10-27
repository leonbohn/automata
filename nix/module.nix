self:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.services.automata-bench;
  inherit (lib) mkOption mkEnableOption mkIf types;
  stateDir = "/var/lib/automata-bench";
in
{
  options.services.automata-bench = {
    enable = mkEnableOption "the automata benchmark service: it runs benchmarks for labelled pull requests and for the main branch, and keeps their history";

    package = mkOption {
      type = types.package;
      default = self.packages.${pkgs.stdenv.hostPlatform.system}.automata-bench;
      defaultText = lib.literalExpression "automata.packages.\${system}.automata-bench";
    };

    repo = mkOption {
      type = types.str;
      default = "leonbohn/automata";
      description = "GitHub repository as `owner/name`.";
    };

    mainBranch = mkOption {
      type = types.str;
      default = "main";
    };

    label = mkOption {
      type = types.str;
      default = "performance";
      description = "Pull requests with this label are benchmarked.";
    };

    allowedLabelers = mkOption {
      type = types.listOf types.str;
      default = [ ];
      description = ''
        GitHub users whose labelling starts a run. This is the trust boundary: the pull request's
        code is built and executed on this machine. Defaults to the owner of the repository.
      '';
    };

    allowForks = mkOption {
      type = types.bool;
      default = false;
      description = "Also run labelled pull requests that come from forks.";
    };

    listenAddress = mkOption {
      type = types.str;
      default = "127.0.0.1";
    };

    port = mkOption {
      type = types.port;
      default = 8742;
    };

    webhookSecretFile = mkOption {
      type = types.str;
      description = "File containing the secret configured on the GitHub webhook (e.g. a sops secret path).";
    };

    githubTokenFile = mkOption {
      type = types.nullOr types.str;
      default = null;
      description = ''
        File containing a GitHub token that may write pull request comments and commit statuses
        (fine-grained: "Pull requests" and "Commit statuses" write access on the repository).
        Without it results are recorded and shown on the dashboard, but not reported on the PR.
      '';
    };

    virtualHost = mkOption {
      type = types.nullOr types.str;
      default = null;
      example = "bench.lnbhn.xyz";
      description = ''
        If set, nginx serves the dashboard on this host and forwards `/webhook` to the service.
        The webhook URL to configure on GitHub is then `https://<virtualHost>/webhook`.
      '';
    };

    cpu = mkOption {
      type = types.nullOr types.str;
      default = null;
      example = "2";
      description = "CPU list to pin the benchmarks to (`taskset -c`). Ideally one that nothing else uses.";
    };

    rounds = mkOption {
      type = types.ints.positive;
      default = 3;
      description = "Alternating rounds per revision. More rounds are slower but filter out noise.";
    };

    threshold = mkOption {
      type = types.numbers.positive;
      default = 10;
      description = "Relative change in percent above which a difference is reported.";
    };

    benches = mkOption {
      type = types.listOf types.str;
      default = [
        "baseline"
        "scc"
        "operations"
        "dpa"
      ];
      description = "Bench targets to run, those a revision does not define are skipped.";
    };

    criterionArgs = mkOption {
      type = types.listOf types.str;
      default = [ "--quick" ];
    };

    memoryMax = mkOption {
      type = types.nullOr types.str;
      default = null;
      example = "6G";
    };
  };

  config = mkIf cfg.enable {
    users.users.automata-bench = {
      isSystemUser = true;
      group = "automata-bench";
      home = stateDir;
    };
    users.groups.automata-bench = { };

    systemd.services.automata-bench = {
      description = "automata benchmark service";
      wantedBy = [ "multi-user.target" ];
      after = [ "network-online.target" ];
      wants = [ "network-online.target" ];

      environment = {
        HOME = stateDir;
        CARGO_HOME = "${stateDir}/cargo";
        RUST_LOG = "info";
      };

      serviceConfig = {
        ExecStart = lib.escapeShellArgs (
          [
            "${cfg.package}/bin/automata-bench"
            "serve"
            "--listen=${cfg.listenAddress}:${toString cfg.port}"
            "--state-dir=${stateDir}"
            "--repo=${cfg.repo}"
            "--main-branch=${cfg.mainBranch}"
            "--label=${cfg.label}"
            "--rounds=${toString cfg.rounds}"
            "--threshold=${toString cfg.threshold}"
            "--webhook-secret-file=%d/webhook-secret"
          ]
          ++ map (u: "--allowed-labeler=${u}") cfg.allowedLabelers
          ++ lib.optional cfg.allowForks "--allow-forks"
          ++ lib.optional (cfg.githubTokenFile != null) "--github-token-file=%d/github-token"
          ++ lib.optional (cfg.virtualHost != null) "--public-url=https://${cfg.virtualHost}/"
          ++ lib.optional (cfg.cpu != null) "--cpu=${cfg.cpu}"
          # the default bench list is replaced, not extended, so it is always passed
          ++ map (b: "--bench=${b}") cfg.benches
          ++ map (a: "--criterion-arg=${a}") cfg.criterionArgs
        );

        LoadCredential = [
          "webhook-secret:${cfg.webhookSecretFile}"
        ]
        ++ lib.optional (cfg.githubTokenFile != null) "github-token:${cfg.githubTokenFile}";

        User = "automata-bench";
        Group = "automata-bench";
        StateDirectory = "automata-bench";
        # the web server reads the dashboard from here
        StateDirectoryMode = "0755";
        UMask = "0022";
        WorkingDirectory = stateDir;
        Restart = "on-failure";
        RestartSec = 10;
        MemoryMax = mkIf (cfg.memoryMax != null) cfg.memoryMax;

        # Pull request code is compiled and run by this service.
        NoNewPrivileges = true;
        ProtectSystem = "strict";
        ProtectHome = true;
        PrivateTmp = true;
        PrivateDevices = true;
        ProtectKernelTunables = true;
        ProtectKernelModules = true;
        ProtectControlGroups = true;
        ProtectClock = true;
        RestrictSUIDSGID = true;
        RestrictNamespaces = true;
        LockPersonality = true;
        RestrictAddressFamilies = [
          "AF_INET"
          "AF_INET6"
          "AF_UNIX"
        ];
        CapabilityBoundingSet = "";
      };
    };

    services.nginx = mkIf (cfg.virtualHost != null) {
      enable = true;
      virtualHosts.${cfg.virtualHost} = {
        forceSSL = true;
        enableACME = true;
        locations."/" = {
          root = "${stateDir}/www";
          index = "index.html";
        };
        locations."= /webhook" = {
          proxyPass = "http://${cfg.listenAddress}:${toString cfg.port}";
          extraConfig = ''
            client_max_body_size 5m;
          '';
        };
      };
    };
  };
}
