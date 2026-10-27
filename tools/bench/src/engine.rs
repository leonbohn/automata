//! Checks out revisions, builds and runs their benchmarks.
//!
//! Every revision is measured exactly once: instruction counts do not need repetitions. The
//! gungraun targets give the numbers that are compared; the criterion target is run afterwards
//! for the wall-clock times that only appear in the detail view.

use crate::model::{EnvInfo, Measured};
use crate::{criterion, gungraun};
use anyhow::{Context, Result, bail};
use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

#[derive(Debug, Clone)]
pub struct Engine {
    /// The git directory (bare mirror or `.git`) the revisions are taken from.
    pub git_dir: PathBuf,
    /// Scratch space for worktrees and cargo target directories; persists between runs so
    /// that dependencies are built only once.
    pub work_dir: PathBuf,
    /// Gungraun bench targets to run, if the revision defines them.
    pub benches: Vec<String>,
    /// The criterion target with the wall-clock times, if the revision defines it.
    pub wallclock_bench: Option<String>,
    pub criterion_args: Vec<String>,
    pub cpu: Option<String>,
}

pub struct Measurement {
    pub results: std::collections::BTreeMap<String, Measured>,
    pub env: EnvInfo,
}

/// Lets a caller stop a running measurement and follow what it does.
#[derive(Debug, Clone, Default)]
pub struct Control {
    pub cancel: Arc<AtomicBool>,
    /// Output of the builds and benchmarks is appended here.
    pub log: Option<PathBuf>,
}

/// The error of a measurement that was stopped on request.
#[derive(Debug)]
pub struct Cancelled;

impl std::fmt::Display for Cancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "cancelled")
    }
}

impl std::error::Error for Cancelled {}

impl Control {
    fn note(&self, line: &str) {
        tracing::info!("{line}");
        if let Some(log) = &self.log
            && let Ok(mut f) = OpenOptions::new().create(true).append(true).open(log)
        {
            let _ = writeln!(f, "== {line}");
        }
    }

    fn stderr(&self) -> Stdio {
        self.log
            .as_ref()
            .and_then(|log| OpenOptions::new().create(true).append(true).open(log).ok())
            .map(Stdio::from)
            .unwrap_or_else(Stdio::null)
    }

    /// Runs a command to completion in its own process group, which is killed on cancellation.
    /// Returns its standard output; standard error goes to the log.
    pub fn run(&self, cmd: &mut Command, what: &str) -> Result<String> {
        use std::os::unix::process::CommandExt;
        if self.cancel.load(Ordering::SeqCst) {
            return Err(Cancelled.into());
        }
        let stdout_path = std::env::temp_dir().join(format!(
            "automata-bench-{}-{}.out",
            std::process::id(),
            std::thread::current().name().unwrap_or("main")
        ));
        let stdout = std::fs::File::create(&stdout_path)?;
        let mut child = cmd
            .stdin(Stdio::null())
            .stdout(stdout)
            .stderr(self.stderr())
            .process_group(0)
            .spawn()
            .with_context(|| format!("starting {what}"))?;
        let status = loop {
            if let Some(status) = child.try_wait()? {
                break status;
            }
            if self.cancel.load(Ordering::SeqCst) {
                // a negative pid addresses the whole process group: cargo, the benchmark, valgrind
                let _ = Command::new("kill")
                    .args(["-KILL", &format!("-{}", child.id())])
                    .status();
                let _ = child.wait();
                let _ = std::fs::remove_file(&stdout_path);
                return Err(Cancelled.into());
            }
            std::thread::sleep(Duration::from_millis(200));
        };
        let out = std::fs::read_to_string(&stdout_path).unwrap_or_default();
        let _ = std::fs::remove_file(&stdout_path);
        if !status.success() {
            let tail = self
                .log
                .as_ref()
                .and_then(|log| std::fs::read_to_string(log).ok())
                .map(|text| {
                    let lines: Vec<&str> = text.lines().rev().take(40).collect();
                    lines.into_iter().rev().collect::<Vec<_>>().join("\n")
                })
                .unwrap_or_default();
            bail!("{what} failed ({status}):\n{tail}");
        }
        Ok(out.trim().to_string())
    }
}

fn quick(cmd: &mut Command, what: &str) -> Result<String> {
    let out = cmd.output().with_context(|| format!("starting {what}"))?;
    if !out.status.success() {
        bail!(
            "{what} failed ({}):\n{}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

impl Engine {
    fn git(&self) -> Command {
        let mut cmd = Command::new("git");
        cmd.arg("--git-dir").arg(&self.git_dir);
        cmd
    }

    pub fn resolve(&self, rev: &str) -> Result<String> {
        quick(
            self.git()
                .args(["rev-parse", "--verify", &format!("{rev}^{{commit}}")]),
            &format!("resolving {rev}"),
        )
    }

    pub fn merge_base(&self, a: &str, b: &str) -> Result<String> {
        quick(self.git().args(["merge-base", a, b]), "git merge-base")
    }

    fn checkout(&self, role: &str, sha: &str) -> Result<PathBuf> {
        let path = self.work_dir.join(format!("src-{role}"));
        // an earlier run may have left a worktree behind
        let _ = self
            .git()
            .args(["worktree", "remove", "--force"])
            .arg(&path)
            .output();
        if path.exists() {
            std::fs::remove_dir_all(&path)?;
        }
        let _ = self.git().args(["worktree", "prune"]).output();
        quick(
            self.git()
                .args(["worktree", "add", "--force", "--detach"])
                .arg(&path)
                .arg(sha),
            &format!("checking out {sha}"),
        )?;
        Ok(path)
    }

    /// The bench targets (of those wanted) that the checkout actually defines.
    fn defined(src: &Path, wanted: impl Iterator<Item = String>) -> Result<Vec<String>> {
        let manifest: toml::Table = std::fs::read_to_string(src.join("Cargo.toml"))?.parse()?;
        let defined: Vec<&str> = manifest
            .get("bench")
            .and_then(|b| b.as_array())
            .map(|a| a.iter().filter_map(|b| b.get("name")?.as_str()).collect())
            .unwrap_or_default();
        Ok(wanted.filter(|b| defined.contains(&b.as_str())).collect())
    }

    fn cargo(&self, src: &Path, target: &Path, pinned: bool) -> Command {
        let mut cmd = match &self.cpu {
            Some(cpu) if pinned => {
                let mut c = Command::new("taskset");
                c.args(["-c", cpu, "cargo"]);
                c
            }
            _ => Command::new("cargo"),
        };
        cmd.current_dir(src).env("CARGO_TARGET_DIR", target);
        cmd
    }

    /// Measures all `(role, revision)` pairs, one after the other. Roles are labels such as
    /// `head` and `base`.
    pub fn measure(&self, revisions: &[(&str, &str)], control: &Control) -> Result<Measurement> {
        std::fs::create_dir_all(&self.work_dir)?;
        let mut results = std::collections::BTreeMap::new();
        for (role, sha) in revisions {
            results.insert(role.to_string(), self.measure_one(role, sha, control)?);
        }
        Ok(Measurement {
            results,
            env: self.env_info(),
        })
    }

    fn measure_one(&self, role: &str, sha: &str, control: &Control) -> Result<Measured> {
        let src = self.checkout(role, sha)?;
        let target = self.work_dir.join(format!("target-{role}"));
        let gungraun_benches = Self::defined(&src, self.benches.iter().cloned())?;
        if gungraun_benches.is_empty() {
            bail!(
                "none of {:?} is a bench target of this revision",
                self.benches
            );
        }
        let wall = Self::defined(&src, self.wallclock_bench.iter().cloned())?;

        control.note(&format!(
            "{role} {sha}: building {gungraun_benches:?} {wall:?}"
        ));
        let mut build = self.cargo(&src, &target, false);
        build.args(["bench", "--no-run"]);
        for b in gungraun_benches.iter().chain(&wall) {
            build.args(["--bench", b]);
        }
        control.run(&mut build, &format!("building {role}"))?;

        let mut measured = Measured::default();
        for bench in &gungraun_benches {
            control.note(&format!("{role}: running {bench}"));
            let mut cmd = self.cargo(&src, &target, true);
            cmd.args(["bench", "--bench", bench, "--", "--output-format=json"]);
            let out = control.run(&mut cmd, &format!("benchmarking {bench} of {role}"))?;
            measured.results.extend(gungraun::parse(&out)?);
        }
        if let Some(bench) = wall.first() {
            control.note(&format!("{role}: running {bench} (wall clock)"));
            let criterion_dir = target.join("criterion");
            let _ = std::fs::remove_dir_all(&criterion_dir);
            let mut cmd = self.cargo(&src, &target, true);
            cmd.args(["bench", "--bench", bench, "--"])
                .args(&self.criterion_args);
            control.run(&mut cmd, &format!("benchmarking {bench} of {role}"))?;
            measured.wall = criterion::collect(&criterion_dir)?;
        }
        let _ = self
            .git()
            .args(["worktree", "remove", "--force"])
            .arg(&src)
            .output();
        control.note(&format!(
            "{role}: {} benchmarks, {} wall-clock measurements",
            measured.results.len(),
            measured.wall.len()
        ));
        Ok(measured)
    }

    pub fn env_info(&self) -> EnvInfo {
        let sh = |cmd: &str, args: &[&str]| {
            Command::new(cmd)
                .args(args)
                .output()
                .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
                .unwrap_or_default()
        };
        let cpu = std::fs::read_to_string("/proc/cpuinfo")
            .ok()
            .and_then(|s| {
                s.lines()
                    .find(|l| l.starts_with("model name") || l.starts_with("Model"))
                    .and_then(|l| l.split_once(':').map(|(_, v)| v.trim().to_string()))
            })
            .unwrap_or_default();
        EnvInfo {
            host: sh("hostname", &[]),
            cpu,
            kernel: sh("uname", &["-sr"]),
            rustc: sh("rustc", &["-V"]),
            valgrind: sh("valgrind", &["--version"]),
            pinned_cpu: self.cpu.clone(),
        }
    }
}
