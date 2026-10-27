//! Checks out revisions, builds and runs their criterion benchmarks and aggregates the results.
//!
//! When several revisions are measured, the rounds alternate between them (A B, B A, A B, ...)
//! on the same machine, so that slow drift (thermal state, noisy neighbours) hits all of them.

use crate::criterion;
use crate::model::{EnvInfo, Results};
use anyhow::{Context, Result, bail};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Debug, Clone)]
pub struct Engine {
    /// The git directory (bare mirror or `.git`) the revisions are taken from.
    pub git_dir: PathBuf,
    /// Scratch space for worktrees and cargo target directories; persists between runs so
    /// that dependencies are built only once.
    pub work_dir: PathBuf,
    /// Bench targets to run, if the revision defines them.
    pub benches: Vec<String>,
    pub criterion_args: Vec<String>,
    pub rounds: u32,
    pub cpu: Option<String>,
}

pub struct Measurement {
    pub results: BTreeMap<String, Results>,
    pub env: EnvInfo,
}

fn run(cmd: &mut Command, what: &str) -> Result<String> {
    let out = cmd.output().with_context(|| format!("starting {what}"))?;
    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        let tail: Vec<&str> = stderr.lines().rev().take(40).collect();
        let tail: Vec<&str> = tail.into_iter().rev().collect();
        bail!("{what} failed ({}):\n{}", out.status, tail.join("\n"));
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
        run(
            self.git()
                .args(["rev-parse", "--verify", &format!("{rev}^{{commit}}")]),
            &format!("resolving {rev}"),
        )
    }

    pub fn merge_base(&self, a: &str, b: &str) -> Result<String> {
        run(self.git().args(["merge-base", a, b]), "git merge-base")
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
        run(
            self.git()
                .args(["worktree", "add", "--force", "--detach"])
                .arg(&path)
                .arg(sha),
            &format!("checking out {sha}"),
        )?;
        Ok(path)
    }

    /// The configured benches that the checkout actually defines.
    fn benches_of(&self, src: &Path) -> Result<Vec<String>> {
        let manifest: toml::Table = std::fs::read_to_string(src.join("Cargo.toml"))?.parse()?;
        let defined: Vec<&str> = manifest
            .get("bench")
            .and_then(|b| b.as_array())
            .map(|a| a.iter().filter_map(|b| b.get("name")?.as_str()).collect())
            .unwrap_or_default();
        let found: Vec<String> = self
            .benches
            .iter()
            .filter(|b| defined.contains(&b.as_str()))
            .cloned()
            .collect();
        if found.is_empty() {
            bail!(
                "none of {:?} is a bench target of this revision",
                self.benches
            );
        }
        Ok(found)
    }

    fn cargo(
        &self,
        src: &Path,
        target: &Path,
        benches: &[String],
        tail: &[String],
        no_run: bool,
    ) -> Command {
        let mut cmd = match &self.cpu {
            Some(cpu) if !no_run => {
                let mut c = Command::new("taskset");
                c.args(["-c", cpu, "cargo"]);
                c
            }
            _ => Command::new("cargo"),
        };
        cmd.current_dir(src)
            .env("CARGO_TARGET_DIR", target)
            .arg("bench");
        for b in benches {
            cmd.args(["--bench", b]);
        }
        if no_run {
            cmd.arg("--no-run");
        } else {
            cmd.arg("--").args(tail);
        }
        cmd
    }

    /// Measures all `(role, revision)` pairs. Roles are labels such as `head` and `base`.
    pub fn measure(&self, revisions: &[(&str, &str)]) -> Result<Measurement> {
        std::fs::create_dir_all(&self.work_dir)?;
        struct Prepared {
            role: String,
            src: PathBuf,
            target: PathBuf,
            benches: Vec<String>,
        }
        let mut prepared = Vec::new();
        for (role, sha) in revisions {
            let src = self.checkout(role, sha)?;
            let benches = self.benches_of(&src)?;
            let target = self.work_dir.join(format!("target-{role}"));
            tracing::info!(role, sha, ?benches, "building");
            run(
                &mut self.cargo(&src, &target, &benches, &[], true),
                &format!("building {role}"),
            )?;
            prepared.push(Prepared {
                role: role.to_string(),
                src,
                target,
                benches,
            });
        }

        let mut samples: BTreeMap<String, Vec<_>> = BTreeMap::new();
        for round in 0..self.rounds.max(1) {
            let mut order: Vec<&Prepared> = prepared.iter().collect();
            if round % 2 == 1 {
                order.reverse();
            }
            for p in order {
                tracing::info!(role = %p.role, round, "benchmarking");
                let criterion_dir = p.target.join("criterion");
                let _ = std::fs::remove_dir_all(&criterion_dir);
                run(
                    &mut self.cargo(&p.src, &p.target, &p.benches, &self.criterion_args, false),
                    &format!("benchmarking {}", p.role),
                )?;
                samples
                    .entry(p.role.clone())
                    .or_default()
                    .push(criterion::collect(&criterion_dir)?);
            }
        }
        for p in &prepared {
            let _ = self
                .git()
                .args(["worktree", "remove", "--force"])
                .arg(&p.src)
                .output();
        }
        Ok(Measurement {
            results: samples
                .iter()
                .map(|(k, v)| (k.clone(), criterion::aggregate(v)))
                .collect(),
            env: self.env_info(),
        })
    }

    fn env_info(&self) -> EnvInfo {
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
            pinned_cpu: self.cpu.clone(),
            criterion_args: self.criterion_args.clone(),
        }
    }
}
