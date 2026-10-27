//! The webhook receiver and the worker that processes queued runs.

use crate::compare;
use crate::db::{Db, NewRun, Run};
use crate::engine::Engine;
use crate::github::Github;
use crate::{render, report};
use anyhow::{Context, Result, bail};
use hmac::{Hmac, Mac};
use serde_json::Value;
use sha2::Sha256;
use std::io::Read;
use std::path::PathBuf;
use std::time::Duration;

#[derive(Clone)]
pub struct Config {
    pub listen: String,
    pub state_dir: PathBuf,
    pub repo: String,
    pub main_branch: String,
    pub label: String,
    /// GitHub users whose `labeled` events are trusted to start a run.
    pub allowed_labelers: Vec<String>,
    pub allow_forks: bool,
    pub webhook_secret: String,
    pub github_token: Option<String>,
    pub public_url: String,
    pub threshold: f64,
    pub engine: Engine,
}

impl Config {
    fn mirror(&self) -> PathBuf {
        self.state_dir.join("mirror.git")
    }
    fn db(&self) -> Result<Db> {
        Db::open(&self.state_dir.join("bench.sqlite"))
    }
    fn www(&self) -> PathBuf {
        self.state_dir.join("www")
    }
}

pub fn verify_signature(secret: &str, body: &[u8], header: &str) -> bool {
    let Some(sig) = header
        .strip_prefix("sha256=")
        .and_then(|h| hex::decode(h).ok())
    else {
        return false;
    };
    let mut mac =
        Hmac::<Sha256>::new_from_slice(secret.as_bytes()).expect("hmac accepts any key length");
    mac.update(body);
    mac.verify_slice(&sig).is_ok()
}

/// Decides what a webhook delivery means. Returns a description of what happened.
pub fn handle_event(cfg: &Config, db: &Db, event: &str, payload: &Value) -> Result<String> {
    if payload["repository"]["full_name"].as_str() != Some(cfg.repo.as_str()) {
        bail!("event for another repository");
    }
    match event {
        "ping" => Ok("pong".into()),
        "push" => {
            let reference = payload["ref"].as_str().unwrap_or_default();
            let sha = payload["after"].as_str().unwrap_or_default();
            if reference != format!("refs/heads/{}", cfg.main_branch)
                || sha.chars().all(|c| c == '0')
            {
                return Ok("ignored push".into());
            }
            let queued = db.enqueue(&NewRun {
                kind: "main".into(),
                pr: None,
                title: payload["head_commit"]["message"]
                    .as_str()
                    .unwrap_or_default()
                    .lines()
                    .next()
                    .unwrap_or_default()
                    .into(),
                head_sha: sha.into(),
            })?;
            Ok(format!(
                "main {sha}: {}",
                if queued.is_some() {
                    "queued"
                } else {
                    "already known"
                }
            ))
        }
        "pull_request" => {
            let action = payload["action"].as_str().unwrap_or_default();
            let pr = &payload["pull_request"];
            let number = pr["number"].as_u64().context("pull request number")?;
            let labelled = pr["labels"]
                .as_array()
                .is_some_and(|l| l.iter().any(|l| l["name"] == cfg.label.as_str()));
            let trusted = match action {
                // a label counts if a trusted user applied it
                "labeled" => {
                    payload["label"]["name"] == cfg.label.as_str()
                        && payload["sender"]["login"].as_str().is_some_and(|u| {
                            cfg.allowed_labelers
                                .iter()
                                .any(|a| a.eq_ignore_ascii_case(u))
                        })
                }
                // later pushes inherit the trust given when the label was applied
                "synchronize" | "reopened" => labelled,
                "unlabeled" if payload["label"]["name"] == cfg.label.as_str() => {
                    db.cancel_pr(number)?;
                    return Ok(format!("PR #{number}: cancelled queued runs"));
                }
                "closed" => {
                    db.cancel_pr(number)?;
                    return Ok(format!("PR #{number}: closed"));
                }
                _ => return Ok("ignored pull_request action".into()),
            };
            if !trusted {
                return Ok(format!("PR #{number}: not labelled by a trusted user"));
            }
            if !cfg.allow_forks
                && pr["head"]["repo"]["full_name"].as_str() != Some(cfg.repo.as_str())
            {
                return Ok(format!(
                    "PR #{number}: comes from a fork, not running its code"
                ));
            }
            let sha = pr["head"]["sha"].as_str().context("head sha")?;
            let queued = db.enqueue(&NewRun {
                kind: "pr".into(),
                pr: Some(number),
                title: pr["title"].as_str().unwrap_or_default().into(),
                head_sha: sha.into(),
            })?;
            Ok(format!(
                "PR #{number} @ {sha}: {}",
                if queued.is_some() {
                    "queued"
                } else {
                    "already known"
                }
            ))
        }
        other => Ok(format!("ignored event {other}")),
    }
}

pub fn serve(cfg: Config) -> Result<()> {
    std::fs::create_dir_all(&cfg.state_dir)?;
    let db = cfg.db()?;
    db.recover()?;
    render::render(&db, &cfg.www(), &cfg.repo, cfg.threshold)?;

    let worker_cfg = cfg.clone();
    std::thread::Builder::new()
        .name("worker".into())
        .spawn(move || worker(worker_cfg))?;

    let server = tiny_http::Server::http(&cfg.listen).map_err(|e| anyhow::anyhow!("{e}"))?;
    tracing::info!(listen = %cfg.listen, repo = %cfg.repo, "waiting for webhooks");
    for mut request in server.incoming_requests() {
        let response = (|| -> Result<(u16, String)> {
            if request.method() != &tiny_http::Method::Post || request.url() != "/webhook" {
                return Ok((404, "not found".into()));
            }
            let header = |name: &str| {
                request
                    .headers()
                    .iter()
                    .find(|h| h.field.as_str().as_str().eq_ignore_ascii_case(name))
                    .map(|h| h.value.to_string())
                    .unwrap_or_default()
            };
            let (signature, event) = (header("X-Hub-Signature-256"), header("X-GitHub-Event"));
            let mut body = Vec::new();
            request.as_reader().take(5_000_000).read_to_end(&mut body)?;
            if !verify_signature(&cfg.webhook_secret, &body, &signature) {
                return Ok((401, "bad signature".into()));
            }
            let payload: Value = serde_json::from_slice(&body).context("payload is not JSON")?;
            match handle_event(&cfg, &db, &event, &payload) {
                Ok(msg) => {
                    tracing::info!("{event}: {msg}");
                    let _ = render::render(&db, &cfg.www(), &cfg.repo, cfg.threshold);
                    Ok((200, msg))
                }
                Err(e) => {
                    tracing::warn!("{event}: {e:#}");
                    Ok((400, format!("{e:#}")))
                }
            }
        })()
        .unwrap_or_else(|e| (500, format!("{e:#}")));
        let _ = request
            .respond(tiny_http::Response::from_string(response.1).with_status_code(response.0));
    }
    Ok(())
}

fn worker(cfg: Config) {
    let db = match cfg.db() {
        Ok(db) => db,
        Err(e) => {
            tracing::error!("worker cannot open the database: {e:#}");
            return;
        }
    };
    loop {
        match db.claim() {
            Ok(Some(run)) => {
                tracing::info!(id = run.id, kind = %run.kind, sha = %run.head_sha, pr = ?run.pr, "starting run");
                if let Err(e) = process(&cfg, &db, &run) {
                    tracing::error!(id = run.id, "run failed: {e:#}");
                    let msg = format!("{e:#}");
                    let _ = db.fail(run.id, &msg);
                    if let (Some(gh), Some(pr)) = (github(&cfg), run.pr) {
                        let _ = gh.upsert_comment(
                            pr,
                            &report::failure(&run.head_sha, &msg, &cfg.public_url),
                        );
                        let _ = gh.set_status(
                            &run.head_sha,
                            "error",
                            "benchmark run failed",
                            &cfg.public_url,
                        );
                    }
                }
                let _ = render::render(&db, &cfg.www(), &cfg.repo, cfg.threshold);
            }
            Ok(None) => std::thread::sleep(Duration::from_secs(5)),
            Err(e) => {
                tracing::error!("queue: {e:#}");
                std::thread::sleep(Duration::from_secs(30));
            }
        }
    }
}

fn github(cfg: &Config) -> Option<Github> {
    cfg.github_token
        .clone()
        .map(|t| Github::new(t, cfg.repo.clone()))
}

fn update_mirror(cfg: &Config) -> Result<()> {
    let mirror = cfg.mirror();
    let url = format!("https://github.com/{}.git", cfg.repo);
    let status = if mirror.exists() {
        std::process::Command::new("git")
            .arg("--git-dir")
            .arg(&mirror)
            .args(["remote", "update", "--prune"])
            .status()
    } else {
        std::process::Command::new("git")
            .args(["clone", "--mirror", &url])
            .arg(&mirror)
            .status()
    }?;
    if !status.success() {
        bail!("could not update the mirror of {url}");
    }
    Ok(())
}

fn process(cfg: &Config, db: &Db, run: &Run) -> Result<()> {
    let gh = github(cfg);
    update_mirror(cfg)?;
    let engine = Engine {
        git_dir: cfg.mirror(),
        ..cfg.engine.clone()
    };
    let head = engine.resolve(&run.head_sha)?;

    if let (Some(gh), Some(_)) = (&gh, run.pr) {
        let _ = gh.set_status(&head, "pending", "benchmarking", &cfg.public_url);
    }

    match run.pr {
        Some(pr) => {
            let base = engine.merge_base(&format!("refs/heads/{}", cfg.main_branch), &head)?;
            let m = engine.measure(&[("head", &head), ("base", &base)])?;
            db.finish(run.id, Some(&base), &m.env, &m.results)?;
            let rows = compare::compare(&m.results["base"], &m.results["head"], cfg.threshold);
            if let Some(gh) = &gh {
                let url = format!("{}#run-{}", cfg.public_url, run.id);
                let body = report::comment(
                    &rows,
                    &head,
                    &base,
                    &m.env,
                    cfg.threshold,
                    cfg.engine.rounds,
                    &url,
                );
                gh.upsert_comment(pr, &body)?;
                gh.set_status(&head, "success", &compare::summary(&rows), &url)?;
            }
        }
        None => {
            let m = engine.measure(&[("head", &head)])?;
            db.finish(run.id, None, &m.env, &m.results)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn cfg() -> Config {
        Config {
            listen: String::new(),
            state_dir: PathBuf::new(),
            repo: "o/r".into(),
            main_branch: "main".into(),
            label: "performance".into(),
            allowed_labelers: vec!["owner".into()],
            allow_forks: false,
            webhook_secret: "s".into(),
            github_token: None,
            public_url: String::new(),
            threshold: 10.0,
            engine: Engine {
                git_dir: PathBuf::new(),
                work_dir: PathBuf::new(),
                benches: vec![],
                criterion_args: vec![],
                rounds: 1,
                cpu: None,
            },
        }
    }

    fn pr_event(action: &str, sender: &str, fork: bool) -> Value {
        json!({
            "action": action,
            "repository": {"full_name": "o/r"},
            "sender": {"login": sender},
            "label": {"name": "performance"},
            "pull_request": {
                "number": 7, "title": "t",
                "labels": [{"name": "performance"}],
                "head": {"sha": "abc", "repo": {"full_name": if fork { "x/r" } else { "o/r" }}},
            },
        })
    }

    #[test]
    fn signature_is_checked() {
        // computed with: printf 'body' | openssl dgst -sha256 -hmac secret
        let mut mac = Hmac::<Sha256>::new_from_slice(b"secret").unwrap();
        mac.update(b"body");
        let good = format!("sha256={}", hex::encode(mac.finalize().into_bytes()));
        assert!(verify_signature("secret", b"body", &good));
        assert!(!verify_signature("secret", b"bodyx", &good));
        assert!(!verify_signature("other", b"body", &good));
        assert!(!verify_signature("secret", b"body", "sha256=zz"));
    }

    #[test]
    fn only_trusted_labelers_start_runs() {
        let db = Db::open(std::path::Path::new(":memory:")).unwrap();
        let cfg = cfg();
        let msg = handle_event(
            &cfg,
            &db,
            "pull_request",
            &pr_event("labeled", "stranger", false),
        )
        .unwrap();
        assert!(msg.contains("not labelled by a trusted user"));
        assert!(db.claim().unwrap().is_none());
        handle_event(
            &cfg,
            &db,
            "pull_request",
            &pr_event("labeled", "owner", false),
        )
        .unwrap();
        assert_eq!(db.claim().unwrap().unwrap().head_sha, "abc");
    }

    #[test]
    fn forks_are_skipped() {
        let db = Db::open(std::path::Path::new(":memory:")).unwrap();
        let msg = handle_event(
            &cfg(),
            &db,
            "pull_request",
            &pr_event("labeled", "owner", true),
        )
        .unwrap();
        assert!(msg.contains("fork"));
        assert!(db.claim().unwrap().is_none());
    }

    #[test]
    fn pushes_to_main_are_queued() {
        let db = Db::open(std::path::Path::new(":memory:")).unwrap();
        let event =
            json!({"ref": "refs/heads/main", "after": "def", "repository": {"full_name": "o/r"}});
        handle_event(&cfg(), &db, "push", &event).unwrap();
        let run = db.claim().unwrap().unwrap();
        assert_eq!((run.kind.as_str(), run.head_sha.as_str()), ("main", "def"));
        let other =
            json!({"ref": "refs/heads/dev", "after": "def", "repository": {"full_name": "o/r"}});
        handle_event(&cfg(), &db, "push", &other).unwrap();
        assert!(db.claim().unwrap().is_none());
    }
}
