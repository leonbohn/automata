//! Benchmark runner, history database, dashboard and webhook service for `automata`.

mod compare;
mod criterion;
mod db;
mod engine;
mod github;
mod model;
mod render;
mod report;
mod server;

use anyhow::{Context, Result};
use clap::{Args, Parser, Subcommand};
use engine::Engine;
use std::path::PathBuf;

#[derive(Parser)]
#[command(version, about)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Args, Clone)]
struct EngineArgs {
    /// Bench targets to run (those a revision does not define are skipped).
    #[arg(long = "bench", default_values_t = ["baseline".to_string(), "scc".into(), "operations".into(), "dpa".into()])]
    benches: Vec<String>,
    /// Arguments passed to criterion.
    #[arg(long = "criterion-arg", default_values_t = ["--quick".to_string()], allow_hyphen_values = true)]
    criterion_args: Vec<String>,
    /// Number of alternating rounds per revision.
    #[arg(long, default_value_t = 3)]
    rounds: u32,
    /// Pin the benchmarks to this CPU list with `taskset -c`.
    #[arg(long)]
    cpu: Option<String>,
    /// Directory for worktrees and cargo target directories.
    #[arg(long)]
    work_dir: Option<PathBuf>,
}

#[derive(Subcommand)]
enum Command {
    /// Benchmark two revisions of a local repository on this machine and print the comparison.
    Compare {
        /// Revision to compare against.
        #[arg(long, default_value = "main")]
        base: String,
        /// Revision under test.
        #[arg(long, default_value = "HEAD")]
        head: String,
        /// Path inside the repository.
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        /// Changes above this many percent count (if outside the spread of the rounds).
        #[arg(long, default_value_t = 10.0)]
        threshold: f64,
        #[command(flatten)]
        engine: EngineArgs,
    },
    /// Benchmark one revision of a local repository and print the numbers.
    Run {
        #[arg(long, default_value = "HEAD")]
        rev: String,
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        #[command(flatten)]
        engine: EngineArgs,
    },
    /// Receive GitHub webhooks, run benchmarks for labelled pull requests and `main`, keep the
    /// history, serve nothing itself: the dashboard is written to `<state-dir>/www`.
    Serve {
        #[arg(long, env = "AUTOMATA_BENCH_LISTEN", default_value = "127.0.0.1:8742")]
        listen: String,
        #[arg(
            long,
            env = "AUTOMATA_BENCH_STATE_DIR",
            default_value = "/var/lib/automata-bench"
        )]
        state_dir: PathBuf,
        /// `owner/name` of the GitHub repository.
        #[arg(long, default_value = "leonbohn/automata")]
        repo: String,
        #[arg(long, default_value = "main")]
        main_branch: String,
        /// Pull requests with this label are benchmarked.
        #[arg(long, default_value = "performance")]
        label: String,
        /// GitHub users whose labelling starts a run (default: the owner of the repository).
        #[arg(long = "allowed-labeler")]
        allowed_labelers: Vec<String>,
        /// Also run code from forks (once a trusted user labelled them).
        #[arg(long)]
        allow_forks: bool,
        #[arg(long)]
        webhook_secret_file: PathBuf,
        /// Token with `Pull requests` and `Commit statuses` write access; without it, results
        /// are only recorded.
        #[arg(long)]
        github_token_file: Option<PathBuf>,
        /// Where the dashboard is reachable, used in links.
        #[arg(long, default_value = "")]
        public_url: String,
        #[arg(long, default_value_t = 10.0)]
        threshold: f64,
        #[command(flatten)]
        engine: EngineArgs,
    },
}

fn read_secret(path: &PathBuf) -> Result<String> {
    Ok(std::fs::read_to_string(path)
        .with_context(|| format!("reading {}", path.display()))?
        .trim()
        .to_string())
}

fn local_engine(repo: &PathBuf, args: &EngineArgs) -> Result<Engine> {
    let out = std::process::Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(["rev-parse", "--path-format=absolute", "--git-common-dir"])
        .output()?;
    anyhow::ensure!(
        out.status.success(),
        "{} is not a git repository",
        repo.display()
    );
    Ok(engine_from(
        PathBuf::from(String::from_utf8(out.stdout)?.trim()),
        args,
    ))
}

fn engine_from(git_dir: PathBuf, args: &EngineArgs) -> Engine {
    Engine {
        work_dir: args
            .work_dir
            .clone()
            .unwrap_or_else(|| git_dir.join("automata-bench")),
        git_dir,
        benches: args.benches.clone(),
        criterion_args: args.criterion_args.clone(),
        rounds: args.rounds,
        cpu: args.cpu.clone(),
    }
}

fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()),
        )
        .with_ansi(std::io::IsTerminal::is_terminal(&std::io::stderr()))
        .with_writer(std::io::stderr)
        .init();
    match Cli::parse().command {
        Command::Compare {
            base,
            head,
            repo,
            threshold,
            engine,
        } => {
            let engine = local_engine(&repo, &engine)?;
            let (base, head) = (engine.resolve(&base)?, engine.resolve(&head)?);
            let m = engine.measure(&[("head", &head), ("base", &base)])?;
            let rows = compare::compare(&m.results["base"], &m.results["head"], threshold);
            println!(
                "{}",
                report::comment(&rows, &head, &base, &m.env, threshold, engine.rounds, "")
            );
        }
        Command::Run { rev, repo, engine } => {
            let engine = local_engine(&repo, &engine)?;
            let rev = engine.resolve(&rev)?;
            let m = engine.measure(&[("head", &rev)])?;
            println!("| benchmark | mean | range |\n|---|--:|--:|");
            for (name, e) in &m.results["head"] {
                println!(
                    "| `{name}` | {} | {} … {} |",
                    model::fmt_ns(e.mean_ns),
                    model::fmt_ns(e.min_ns),
                    model::fmt_ns(e.max_ns)
                );
            }
            println!(
                "\n{} · {} · {} · {} rounds",
                m.env.host, m.env.cpu, m.env.rustc, engine.rounds
            );
        }
        Command::Serve {
            listen,
            state_dir,
            repo,
            main_branch,
            label,
            mut allowed_labelers,
            allow_forks,
            webhook_secret_file,
            github_token_file,
            public_url,
            threshold,
            engine,
        } => {
            if allowed_labelers.is_empty() {
                allowed_labelers.push(repo.split('/').next().unwrap_or_default().to_string());
            }
            let args_work_dir = engine.work_dir.clone();
            let mut engine = engine_from(state_dir.join("mirror.git"), &engine);
            engine.work_dir = args_work_dir.unwrap_or_else(|| state_dir.join("work"));
            server::serve(server::Config {
                listen,
                repo,
                main_branch,
                label,
                allowed_labelers,
                allow_forks,
                webhook_secret: read_secret(&webhook_secret_file)?,
                github_token: github_token_file.as_ref().map(read_secret).transpose()?,
                public_url,
                threshold,
                engine,
                state_dir,
            })?;
        }
    }
    Ok(())
}
