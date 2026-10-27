//! The web server (webhooks, dashboard, controls) and the worker that processes queued runs.

use crate::db::{Db, NewRun, Run};
use crate::engine::{Cancelled, Control, Engine};
use crate::github::Github;
use crate::model::{Measured, Metric};
use crate::web::{self, Site};
use crate::{compare, report};
use anyhow::{Context, Result, bail};
use hmac::{Hmac, Mac};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::io::Read;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

const HTMX: &[u8] = include_bytes!("../static/htmx.min.js");
const STYLE: &str = include_str!("../static/style.css");

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
    /// Token that authorizes cancelling and discarding runs. Without it the controls of the
    /// dashboard are disabled.
    pub admin_token: Option<String>,
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
    fn logs(&self) -> PathBuf {
        self.state_dir.join("logs")
    }
}

/// The run that is being processed, so that it can be stopped from a request.
#[derive(Default)]
pub struct Shared {
    running: Mutex<Option<(i64, Arc<AtomicBool>)>>,
}

impl Shared {
    /// Asks the running run to stop. Returns whether `id` is the run that is going.
    fn cancel(&self, id: i64) -> bool {
        match &*self.running.lock().expect("lock") {
            Some((running, flag)) if *running == id => {
                flag.store(true, Ordering::SeqCst);
                true
            }
            _ => false,
        }
    }
}

fn digest(s: &str) -> [u8; 32] {
    Sha256::digest(s.as_bytes()).into()
}

/// Compares in constant time (of the digests, which hides the length too).
fn token_matches(expected: &str, given: &str) -> bool {
    digest(expected)
        .iter()
        .zip(digest(given))
        .fold(0u8, |acc, (a, b)| acc | (a ^ b))
        == 0
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
            // every commit of the push gets a point in the history, oldest first
            let mut commits: Vec<(String, String)> = payload["commits"]
                .as_array()
                .map(|cs| {
                    cs.iter()
                        .filter_map(|c| {
                            Some((
                                c["id"].as_str()?.to_string(),
                                c["message"]
                                    .as_str()
                                    .unwrap_or_default()
                                    .lines()
                                    .next()
                                    .unwrap_or_default()
                                    .to_string(),
                            ))
                        })
                        .collect()
                })
                .unwrap_or_default();
            if !commits.iter().any(|(id, _)| id == sha) {
                commits.push((
                    sha.to_string(),
                    payload["head_commit"]["message"]
                        .as_str()
                        .unwrap_or_default()
                        .lines()
                        .next()
                        .unwrap_or_default()
                        .to_string(),
                ));
            }
            let mut queued = 0;
            for (id, title) in &commits {
                let run = NewRun {
                    kind: "main".into(),
                    pr: None,
                    title: title.clone(),
                    head_sha: id.clone(),
                };
                queued += usize::from(db.enqueue(&run)?.is_some());
            }
            Ok(format!(
                "main {sha}: {queued} of {} commits queued",
                commits.len()
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

/// A request, reduced to what the router looks at.
pub struct Req {
    pub method: String,
    /// Path and query.
    pub url: String,
    pub authorization: String,
    pub signature: String,
    pub event: String,
    pub body: Vec<u8>,
}

pub struct Reply {
    pub status: u16,
    pub content_type: &'static str,
    pub body: Vec<u8>,
}

impl Reply {
    fn html(body: String) -> Self {
        Self {
            status: 200,
            content_type: "text/html; charset=utf-8",
            body: body.into_bytes(),
        }
    }
    fn text(status: u16, body: impl Into<String>) -> Self {
        Self {
            status,
            content_type: "text/plain; charset=utf-8",
            body: body.into().into_bytes(),
        }
    }
}

/// The value of `key` in a query string or a form body.
fn param(query: &str, key: &str) -> String {
    query
        .split('&')
        .filter_map(|kv| kv.split_once('='))
        .find(|(k, _)| *k == key)
        .map(|(_, v)| percent_decode(v))
        .unwrap_or_default()
}

fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'+' => out.push(b' '),
            b'%' if i + 2 < bytes.len() => match u8::from_str_radix(&s[i + 1..i + 3], 16) {
                Ok(b) => {
                    out.push(b);
                    i += 2;
                }
                Err(_) => out.push(b'%'),
            },
            b => out.push(b),
        }
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

pub fn route(cfg: &Config, shared: &Shared, db: &Db, req: &Req) -> Reply {
    let (path, query) = req.url.split_once('?').unwrap_or((req.url.as_str(), ""));
    let site = Site {
        db,
        repo: &cfg.repo,
        threshold: cfg.threshold,
    };
    let result = (|| -> Result<Reply> {
        let method = req.method.as_str();
        let segments: Vec<&str> = path.trim_matches('/').split('/').collect();

        // webhooks authenticate with their signature
        if (method, path) == ("POST", "/webhook") {
            if !verify_signature(&cfg.webhook_secret, &req.body, &req.signature) {
                return Ok(Reply::text(401, "bad signature"));
            }
            let payload: Value =
                serde_json::from_slice(&req.body).context("payload is not JSON")?;
            return Ok(match handle_event(cfg, db, &req.event, &payload) {
                Ok(msg) => {
                    tracing::info!("{}: {msg}", req.event);
                    Reply::text(200, msg)
                }
                Err(e) => {
                    tracing::warn!("{}: {e:#}", req.event);
                    Reply::text(400, format!("{e:#}"))
                }
            });
        }

        // everything that changes something needs the admin token
        if method != "GET" {
            match &cfg.admin_token {
                None => return Ok(Reply::text(403, "no admin token is configured")),
                Some(token) => {
                    let given = req
                        .authorization
                        .strip_prefix("Bearer ")
                        .unwrap_or_default();
                    if !token_matches(token, given) {
                        return Ok(Reply::text(401, "missing or wrong admin token"));
                    }
                }
            }
        }

        Ok(match (method, segments.as_slice()) {
            ("GET", [""]) => Reply::html(site.index()?),
            ("GET", ["fragments", "queue"]) => Reply::html(site.queue()?),
            ("GET", ["fragments", "history"]) => Reply::html(site.history(
                Metric::parse(&param(query, "metric")),
                &param(query, "group"),
                &param(query, "q"),
            )?),
            ("GET", ["fragments", "log", id]) => {
                let id: i64 = id.parse().context("run id")?;
                Reply::html(charts_esc(&web::log_tail(
                    &cfg.logs().join(format!("{id}.log")),
                )))
            }
            ("GET", ["run", id]) => {
                let page = match id.parse::<i64>() {
                    Ok(id) => site.run(id, &cfg.logs())?,
                    Err(_) => None,
                };
                match page {
                    Some(page) => Reply::html(page),
                    None => Reply::text(404, "no such run"),
                }
            }
            ("GET", ["data.json"]) => Reply {
                status: 200,
                content_type: "application/json",
                body: serde_json::to_vec_pretty(&db.history(Metric::Instructions, 1000)?)?,
            },
            ("GET", ["static", "htmx.min.js"]) => Reply {
                status: 200,
                content_type: "text/javascript",
                body: HTMX.to_vec(),
            },
            ("GET", ["static", "style.css"]) => Reply {
                status: 200,
                content_type: "text/css",
                body: STYLE.as_bytes().to_vec(),
            },

            ("POST", ["runs", id, "cancel"]) => {
                let id: i64 = id.parse().context("run id")?;
                if !shared.cancel(id) {
                    return Ok(Reply::text(409, "that run is not running"));
                }
                tracing::info!(id, "cancelling the running run");
                Reply::html(site.queue()?)
            }
            ("DELETE", ["queue", id]) => {
                let id: i64 = id.parse().context("run id")?;
                if !db.discard(id)? {
                    return Ok(Reply::text(409, "that run is not queued"));
                }
                tracing::info!(id, "discarded from the queue");
                Reply::html(site.queue()?)
            }
            ("DELETE", ["queue"]) => {
                let n = db.discard_all()?;
                tracing::info!(n, "discarded everything that was queued");
                Reply::html(site.queue()?)
            }
            ("POST", ["queue"]) => {
                let sha = param(&String::from_utf8_lossy(&req.body), "sha");
                if sha.len() < 7 || !sha.chars().all(|c| c.is_ascii_hexdigit()) {
                    return Ok(Reply::text(400, "expected a commit hash"));
                }
                db.enqueue(&NewRun {
                    kind: "main".into(),
                    pr: None,
                    title: "queued by hand".into(),
                    head_sha: sha,
                })?;
                Reply::html(site.queue()?)
            }
            _ => Reply::text(404, "not found"),
        })
    })();
    result.unwrap_or_else(|e| Reply::text(500, format!("{e:#}")))
}

fn charts_esc(s: &str) -> String {
    crate::charts::esc(s)
}

pub fn serve(cfg: Config) -> Result<()> {
    std::fs::create_dir_all(cfg.logs())?;
    let db = cfg.db()?;
    db.recover()?;
    let shared = Arc::new(Shared::default());

    let (worker_cfg, worker_shared) = (cfg.clone(), shared.clone());
    std::thread::Builder::new()
        .name("worker".into())
        .spawn(move || worker(worker_cfg, worker_shared))?;

    let server = tiny_http::Server::http(&cfg.listen).map_err(|e| anyhow::anyhow!("{e}"))?;
    tracing::info!(listen = %cfg.listen, repo = %cfg.repo, "serving the dashboard and webhooks");
    for mut request in server.incoming_requests() {
        let header = |name: &str| {
            request
                .headers()
                .iter()
                .find(|h| h.field.as_str().as_str().eq_ignore_ascii_case(name))
                .map(|h| h.value.to_string())
                .unwrap_or_default()
        };
        let mut req = Req {
            method: request.method().as_str().to_string(),
            url: request.url().to_string(),
            authorization: header("Authorization"),
            signature: header("X-Hub-Signature-256"),
            event: header("X-GitHub-Event"),
            body: Vec::new(),
        };
        if request
            .as_reader()
            .take(5_000_000)
            .read_to_end(&mut req.body)
            .is_err()
        {
            continue;
        }
        let reply = route(&cfg, &shared, &db, &req);
        let content_type = tiny_http::Header::from_bytes("Content-Type", reply.content_type)
            .expect("static header");
        let _ = request.respond(
            tiny_http::Response::from_data(reply.body)
                .with_status_code(reply.status)
                .with_header(content_type),
        );
    }
    Ok(())
}

fn worker(cfg: Config, shared: Arc<Shared>) {
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
                let control = Control {
                    cancel: Arc::new(AtomicBool::new(false)),
                    log: Some(cfg.logs().join(format!("{}.log", run.id))),
                };
                if let Some(log) = &control.log {
                    let _ = std::fs::remove_file(log);
                }
                *shared.running.lock().expect("lock") = Some((run.id, control.cancel.clone()));
                let outcome = process(&cfg, &db, &run, &control);
                *shared.running.lock().expect("lock") = None;
                if let Err(e) = outcome {
                    let gh = github(&cfg);
                    if e.downcast_ref::<Cancelled>().is_some() {
                        tracing::info!(id = run.id, "run cancelled");
                        let _ = db.mark_cancelled(run.id);
                        if let (Some(gh), Some(_)) = (gh, run.pr) {
                            let _ = gh.set_status(
                                &run.head_sha,
                                "error",
                                "benchmark run cancelled",
                                &cfg.public_url,
                            );
                        }
                    } else {
                        tracing::error!(id = run.id, "run failed: {e:#}");
                        let msg = format!("{e:#}");
                        let _ = db.fail(run.id, &msg);
                        if let (Some(gh), Some(pr)) = (gh, run.pr) {
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
                }
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

fn process(cfg: &Config, db: &Db, run: &Run, control: &Control) -> Result<()> {
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
            // `main` is benchmarked at every commit, so the merge base usually is known already
            let known = db.main_measurement(&base)?;
            let mut m = engine.measure(&[("head", &head)], control)?;
            let base_measured: Measured = match known {
                Some(known) => {
                    tracing::info!(base, "reusing the measurement of the merge base");
                    known
                }
                None => {
                    let mut with_base = engine.measure(&[("base", &base)], control)?;
                    with_base.results.remove("base").unwrap_or_default()
                }
            };
            m.results.insert("base".into(), base_measured);
            db.finish(run.id, Some(&base), &m.env, &m.results)?;
            let rows = compare::compare(
                &m.results["base"].results,
                &m.results["head"].results,
                cfg.threshold,
            );
            if let Some(gh) = &gh {
                let url = format!("{}run/{}", cfg.public_url, run.id);
                let body = report::comment(&rows, &head, &base, &m.env, cfg.threshold, &url);
                gh.upsert_comment(pr, &body)?;
                gh.set_status(&head, "success", &compare::summary(&rows), &url)?;
            }
        }
        None => {
            let m = engine.measure(&[("head", &head)], control)?;
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
            admin_token: Some("tok".into()),
            public_url: String::new(),
            threshold: 1.0,
            engine: Engine {
                git_dir: PathBuf::new(),
                work_dir: PathBuf::new(),
                benches: vec![],
                wallclock_bench: None,
                criterion_args: vec![],
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

    fn req(method: &str, url: &str, token: &str) -> Req {
        Req {
            method: method.into(),
            url: url.into(),
            authorization: if token.is_empty() {
                String::new()
            } else {
                format!("Bearer {token}")
            },
            signature: String::new(),
            event: String::new(),
            body: Vec::new(),
        }
    }

    fn memory_db() -> Db {
        Db::open(std::path::Path::new(":memory:")).unwrap()
    }

    #[test]
    fn every_commit_of_a_push_is_queued_oldest_first() {
        let db = memory_db();
        let event = json!({
            "ref": "refs/heads/main", "after": "c3", "repository": {"full_name": "o/r"},
            "commits": [{"id": "c1", "message": "one\n\nbody"}, {"id": "c2", "message": "two"}, {"id": "c3", "message": "three"}],
        });
        handle_event(&cfg(), &db, "push", &event).unwrap();
        let order: Vec<String> = std::iter::from_fn(|| db.claim().unwrap())
            .map(|r| r.head_sha)
            .collect();
        assert_eq!(order, ["c1", "c2", "c3"]);
    }

    #[test]
    fn controls_need_the_admin_token() {
        let db = memory_db();
        let shared = Shared::default();
        let id = db
            .enqueue(&NewRun {
                kind: "main".into(),
                pr: None,
                title: "t".into(),
                head_sha: "a".into(),
            })
            .unwrap()
            .unwrap();
        let path = format!("/queue/{id}");
        assert_eq!(
            route(&cfg(), &shared, &db, &req("DELETE", &path, "")).status,
            401
        );
        assert_eq!(
            route(&cfg(), &shared, &db, &req("DELETE", &path, "wrong")).status,
            401
        );
        assert_eq!(db.queue().unwrap().len(), 1);
        assert_eq!(
            route(&cfg(), &shared, &db, &req("DELETE", &path, "tok")).status,
            200
        );
        assert!(db.queue().unwrap().is_empty());
        // without a configured token nothing can be changed
        let mut open = cfg();
        open.admin_token = None;
        assert_eq!(
            route(&open, &shared, &db, &req("DELETE", "/queue", "tok")).status,
            403
        );
    }

    #[test]
    fn cancelling_stops_only_the_running_run() {
        let db = memory_db();
        let shared = Shared::default();
        let flag = Arc::new(AtomicBool::new(false));
        *shared.running.lock().unwrap() = Some((5, flag.clone()));
        assert_eq!(
            route(&cfg(), &shared, &db, &req("POST", "/runs/6/cancel", "tok")).status,
            409
        );
        assert!(!flag.load(Ordering::SeqCst));
        assert_eq!(
            route(&cfg(), &shared, &db, &req("POST", "/runs/5/cancel", "tok")).status,
            200
        );
        assert!(flag.load(Ordering::SeqCst));
    }

    #[test]
    fn pages_render_on_an_empty_database() {
        let db = memory_db();
        let shared = Shared::default();
        for url in [
            "/",
            "/fragments/queue",
            "/fragments/history?metric=heap_bytes&q=x",
            "/data.json",
            "/static/style.css",
            "/static/htmx.min.js",
        ] {
            let reply = route(&cfg(), &shared, &db, &req("GET", url, ""));
            assert_eq!(reply.status, 200, "{url}");
        }
        assert_eq!(
            route(&cfg(), &shared, &db, &req("GET", "/run/99", "")).status,
            404
        );
        assert_eq!(
            route(&cfg(), &shared, &db, &req("GET", "/nothing", "")).status,
            404
        );
    }

    #[test]
    fn decodes_form_values() {
        assert_eq!(param("a=1&sha=ab%20c+d", "sha"), "ab c d");
        assert_eq!(param("a=1", "sha"), "");
        assert_eq!(percent_decode("100%"), "100%");
    }
}
