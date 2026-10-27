//! Benchmark runner, history database, dashboard and webhook service for `automata`.

mod charts;
mod compare;
mod criterion;
mod db;
mod engine;
mod github;
mod gungraun;
mod model;
mod report;
mod server;
mod web;

use anyhow::{Context, Result, bail};
use clap::{Args, Parser, Subcommand};
use engine::{Control, Engine};
use std::path::PathBuf;

#[derive(Parser)]
#[command(version, about)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Args, Clone)]
struct EngineArgs {
    /// Gungraun bench targets to run (those a revision does not define are skipped).
    #[arg(long = "bench", default_values_t = ["scc".to_string(), "ts".into(), "runs".into(), "dfa".into(), "dpa".into()])]
    benches: Vec<String>,
    /// The criterion target with the wall-clock times, shown in the detail view only.
    #[arg(long, default_value = "wallclock")]
    wallclock_bench: String,
    /// Do not run the wall-clock target.
    #[arg(long)]
    no_wallclock: bool,
    /// Arguments passed to criterion.
    #[arg(long = "criterion-arg", default_values_t = ["--quick".to_string()], allow_hyphen_values = true)]
    criterion_args: Vec<String>,
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
        /// Changes of the instruction count above this many percent count.
        #[arg(long, default_value_t = 1.0)]
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
    /// Run the suite several times on one revision and fail if the instruction counts differ.
    CheckDeterminism {
        #[arg(long, default_value = "HEAD")]
        rev: String,
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        /// How often the suite is run.
        #[arg(long, default_value_t = 2)]
        runs: usize,
        /// Largest accepted deviation between runs in percent.
        #[arg(long, default_value_t = 0.5)]
        tolerance: f64,
        #[command(flatten)]
        engine: EngineArgs,
    },
    /// Serve the dashboard, receive GitHub webhooks and run benchmarks for labelled pull requests
    /// and for every commit of `main`.
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
        /// File with the token that allows cancelling and discarding runs on the dashboard;
        /// without it the dashboard is read-only.
        #[arg(long)]
        admin_token_file: Option<PathBuf>,
        /// Where the dashboard is reachable, used in links.
        #[arg(long, default_value = "")]
        public_url: String,
        #[arg(long, default_value_t = 1.0)]
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
        wallclock_bench: (!args.no_wallclock).then(|| args.wallclock_bench.clone()),
        criterion_args: args.criterion_args.clone(),
        cpu: args.cpu.clone(),
    }
}

/// A control that writes the output of the commands to stderr's log, for local use.
fn local_control(engine: &Engine) -> Control {
    let log = engine.work_dir.join("last-run.log");
    let _ = std::fs::create_dir_all(&engine.work_dir);
    let _ = std::fs::remove_file(&log);
    eprintln!("output of the builds and benchmarks: {}", log.display());
    Control {
        log: Some(log),
        ..Control::default()
    }
}

/// Benchmarks that executed (almost) no instructions did not measure what they claim to.
fn warn_about_empty(results: &model::Results) {
    for (name, m) in results {
        if m.instructions < 1_000 {
            tracing::warn!("{name} executed only {} instructions", m.instructions);
        }
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
            let m = engine.measure(&[("head", &head), ("base", &base)], &local_control(&engine))?;
            warn_about_empty(&m.results["head"].results);
            let rows = compare::compare(
                &m.results["base"].results,
                &m.results["head"].results,
                threshold,
            );
            println!(
                "{}",
                report::comment(&rows, &head, &base, &m.env, threshold, "")
            );
        }
        Command::Run { rev, repo, engine } => {
            let engine = local_engine(&repo, &engine)?;
            let rev = engine.resolve(&rev)?;
            let m = engine.measure(&[("head", &rev)], &local_control(&engine))?;
            let measured = &m.results["head"];
            warn_about_empty(&measured.results);
            println!(
                "| benchmark | instructions | est. cycles | heap bytes | allocations |\n|---|--:|--:|--:|--:|"
            );
            for (name, e) in &measured.results {
                let opt = |v: Option<u64>| v.map(model::fmt_count).unwrap_or_default();
                println!(
                    "| `{name}` | {} | {} | {} | {} |",
                    model::fmt_count(e.instructions),
                    model::fmt_count(e.estimated_cycles),
                    opt(e.heap_bytes),
                    opt(e.heap_blocks)
                );
            }
            println!(
                "\n{} · {} · {} · {}",
                m.env.host, m.env.cpu, m.env.rustc, m.env.valgrind
            );
            if !measured.wall.is_empty() {
                println!("\n| wall clock | mean |\n|---|--:|");
                for (name, w) in &measured.wall {
                    println!("| `{name}` | {} |", model::fmt_ns(w.mean_ns));
                }
            }
        }
        Command::CheckDeterminism {
            rev,
            repo,
            runs,
            tolerance,
            mut engine,
        } => {
            // wall-clock times are not part of this check
            engine.no_wallclock = true;
            let engine = local_engine(&repo, &engine)?;
            let rev = engine.resolve(&rev)?;
            let mut all = Vec::new();
            for run in 1..=runs.max(2) {
                tracing::info!(run, "running the suite");
                let m = engine.measure(&[("head", &rev)], &local_control(&engine))?;
                all.push(m.results["head"].results.clone());
            }
            let mut worst = (0.0f64, String::new());
            for name in all[0].keys() {
                let values: Vec<u64> = all
                    .iter()
                    .filter_map(|r| r.get(name))
                    .map(|m| m.instructions)
                    .collect();
                let (lo, hi) = (
                    values.iter().min().copied().unwrap_or(0),
                    values.iter().max().copied().unwrap_or(0),
                );
                let spread = compare::relative_change(lo, hi);
                if spread > worst.0 {
                    worst = (spread, name.clone());
                }
            }
            println!(
                "{} benchmarks, {} runs, largest spread {:.3} % ({})",
                all[0].len(),
                all.len(),
                worst.0,
                worst.1
            );
            if worst.0 > tolerance {
                bail!(
                    "the spread of {} is above the tolerance of {tolerance} %",
                    worst.1
                );
            }
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
            admin_token_file,
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
                admin_token: admin_token_file.as_ref().map(read_secret).transpose()?,
                public_url,
                threshold,
                engine,
                state_dir,
            })?;
        }
    }
    Ok(())
}
