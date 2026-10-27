//! The pages of the dashboard. Plain HTML rendered on the server; htmx (version 4) swaps the fragments that
//! change (the queue, the history). There is no client-side state.

use crate::charts::{self, esc};
use crate::compare::{self, Row, Verdict};
use crate::db::{Db, RunInfo};
use crate::model::{Metric, Results, fmt_count, fmt_ns, fmt_short};
use anyhow::Result;
use std::collections::BTreeMap;
use std::fmt::Write;
use std::path::Path;

/// How many commits of `main` the graphs show.
const HISTORY: usize = 200;
/// Cards shown at most, the filter narrows them down.
const MAX_CARDS: usize = 300;

pub struct Site<'a> {
    pub db: &'a Db,
    pub repo: &'a str,
    pub threshold: f64,
}

fn day(t: i64) -> String {
    let (h, m) = ((t.rem_euclid(86_400)) / 3600, (t.rem_euclid(3600)) / 60);
    format!("{} {h:02}:{m:02}", charts::day(t))
}

fn sha_link(repo: &str, sha: &str) -> String {
    format!(
        r#"<a href="https://github.com/{}/commit/{}">{}</a>"#,
        esc(repo),
        esc(sha),
        esc(&sha[..sha.len().min(8)])
    )
}

fn what(run: &RunInfo) -> String {
    match run.pr {
        Some(pr) => format!("PR #{pr}"),
        None => "main".into(),
    }
}

pub fn page(title: &str, body: &str) -> String {
    format!(
        r#"<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{}</title>
<link rel="stylesheet" href="/static/style.css">
<script src="/static/htmx.min.js" defer></script>
</head>
<body>
<h1><a href="/">automata benchmarks</a></h1>
{body}
</body>
</html>
"#,
        esc(title)
    )
}

impl Site<'_> {
    pub fn index(&self) -> Result<String> {
        let mut body = String::new();
        if let Some(run) = self.db.recent_main_runs(1)?.first()
            && let Some(env) = &run.env
        {
            let _ = write!(
                body,
                r#"<p class="mut">{} · {} · {} · {}{}</p>"#,
                esc(&env.cpu),
                esc(&env.rustc),
                esc(&env.valgrind),
                esc(&env.kernel),
                env.pinned_cpu
                    .as_ref()
                    .map(|c| format!(" · pinned to cpu {}", esc(c)))
                    .unwrap_or_default()
            );
        }
        body += r#"<h2>Queue</h2>
<div id="queue" hx-get="/fragments/queue" hx-trigger="load, every 3s">loading…</div>
<h2>Pull requests</h2>
"#;
        body += &self.pull_requests()?;
        body += r##"<h2>History of <code>main</code></h2>
<p class="mut">One point per commit, oldest on the left. Instruction counts are exact, so every visible step is a real change; red and green points changed by more than the threshold.</p>
<form class="filters" hx-get="/fragments/history" hx-target="#history" hx-trigger="change, keyup changed delay:300ms from:#q">
<select name="metric">"##;
        for m in Metric::ALL {
            let _ = write!(
                body,
                r#"<option value="{}">{}</option>"#,
                m.key(),
                m.label()
            );
        }
        body += r#"</select>
<select name="group"><option value="">all benchmark files</option>"#;
        let history = self.db.history(Metric::Instructions, HISTORY)?;
        let mut files: Vec<&str> = history
            .keys()
            .filter_map(|b| b.split("::").next())
            .collect();
        files.dedup();
        for f in files {
            let _ = write!(body, r#"<option value="{0}">{0}</option>"#, esc(f));
        }
        body += r#"</select>
<input id="q" name="q" placeholder="filter benchmarks" autocomplete="off">
</form>
<div id="history" hx-get="/fragments/history" hx-trigger="load">loading…</div>"#;
        Ok(page("automata benchmarks", &body))
    }

    pub fn queue(&self) -> Result<String> {
        let queue = self.db.queue()?;
        if queue.is_empty() {
            return Ok(r#"<p class="mut">Nothing is running or waiting.</p>"#.into());
        }
        let mut out = String::from(
            "<table><tr><th>run</th><th>commit</th><th>title</th><th>status</th></tr>",
        );
        for run in &queue {
            let _ = write!(
                out,
                r#"<tr><td><a href="/run/{id}">{what}</a></td><td>{sha}</td><td>{title}</td><td>{status}</td></tr>"#,
                id = run.id,
                what = what(run),
                sha = sha_link(self.repo, &run.head_sha),
                title = esc(&run.title),
                status = esc(&run.status),
            );
        }
        out += "</table>";
        Ok(out)
    }

    fn pull_requests(&self) -> Result<String> {
        let prs = self.db.pull_requests(self.threshold)?;
        if prs.is_empty() {
            return Ok(r#"<p class="mut">No pull request has been benchmarked yet.</p>"#.into());
        }
        let mut out = String::new();
        for p in prs {
            let n = |v| compare::count(&p.rows, v);
            let summary = if p.info.status == "done" {
                format!(
                    r#"<span class="bad">{} regressions</span>, <span class="good">{} improvements</span>, {} unchanged, {} new"#,
                    n(Verdict::Regression),
                    n(Verdict::Improvement),
                    n(Verdict::Unchanged),
                    n(Verdict::New)
                )
            } else {
                esc(&format!(
                    "{}{}",
                    p.info.status,
                    p.info
                        .error
                        .as_ref()
                        .and_then(|e| e.lines().next().map(|l| format!(": {l}")))
                        .unwrap_or_default()
                ))
            };
            let _ = write!(
                out,
                r#"<p><a href="https://github.com/{repo}/pull/{pr}">#{pr}</a> {title} · {sha} · <a href="/run/{id}">details</a> · {summary}</p>"#,
                repo = esc(self.repo),
                pr = p.info.pr.unwrap_or(0),
                title = esc(&p.info.title),
                sha = sha_link(self.repo, &p.info.head_sha),
                id = p.info.id,
            );
        }
        Ok(out)
    }

    /// The graphs: the stacked chart and one card per benchmark.
    pub fn history(&self, metric: Metric, group: &str, query: &str) -> Result<String> {
        let all = self.db.history(metric, HISTORY)?;
        if all.is_empty() {
            return Ok(format!(
                r#"<p class="mut">No results for {} on <code>main</code> yet.</p>"#,
                esc(metric.label())
            ));
        }
        let in_group: BTreeMap<_, _> = all
            .iter()
            .filter(|(b, _)| group.is_empty() || b.split("::").next() == Some(group))
            .collect();
        let query = query.to_lowercase();
        let matching: Vec<_> = in_group
            .iter()
            .filter(|(b, _)| query.is_empty() || b.to_lowercase().contains(&query))
            .collect();

        // all commits that have a result in the selection, oldest first
        let mut commits: Vec<crate::db::Point> = Vec::new();
        for points in in_group.values() {
            for p in points.iter() {
                if !commits.iter().any(|c| c.run == p.run) {
                    commits.push(crate::db::Point {
                        value: 0,
                        ..p.clone()
                    });
                }
            }
        }
        commits.sort_by_key(|c| c.run);
        let by_file = group.is_empty();
        let bands = charts::align(
            &commits,
            &in_group
                .iter()
                .map(|(k, v)| ((*k).clone(), (*v).clone()))
                .collect(),
            |bench| {
                let mut parts = bench.split("::");
                let file = parts.next().unwrap_or_default();
                if by_file {
                    file.to_string()
                } else {
                    parts.nth(1).unwrap_or_default().to_string()
                }
            },
        );
        let mut out = format!(
            "<h3>{} of {}, stacked</h3>{}",
            esc(metric.label()),
            if group.is_empty() {
                "all benchmarks".into()
            } else {
                esc(group)
            },
            charts::stacked(&commits, &bands)
        );
        let legend: Vec<String> = bands
            .iter()
            .enumerate()
            .map(|(k, b)| {
                format!(
                    r#"<span style="color: hsl({} 55% 55%)">■</span> {}"#,
                    charts::hue(k),
                    esc(&b.name)
                )
            })
            .collect();
        let _ = write!(out, r#"<p class="mut">{}</p>"#, legend.join(" · "));

        let mut current = "";
        for (shown, (name, points)) in matching.into_iter().enumerate() {
            if shown == MAX_CARDS {
                out += r#"<p class="mut">More benchmarks match, narrow the filter.</p>"#;
                break;
            }
            let file_group = name.rsplit_once("::").map(|(g, _)| g).unwrap_or(name);
            if file_group != current {
                if !current.is_empty() {
                    out += "</div>";
                }
                // module paths look like `file::group::function`, where file and group are
                // usually the same word
                let parts: Vec<&str> = file_group.split("::").collect();
                let title = match parts.as_slice() {
                    [file, group, function] if file == group => format!("{file} › {function}"),
                    parts => parts.join(" › "),
                };
                let _ = write!(out, r#"<h3>{}</h3><div class="grid">"#, esc(&title));
                current = file_group;
            }
            let last = points.last().expect("histories are not empty");
            let delta = points
                .len()
                .checked_sub(2)
                .map(|i| compare::relative_change(points[i].value, last.value))
                .filter(|c| c.is_finite() && *c != 0.0)
                .map(|c| {
                    let class = if c > self.threshold {
                        "bad"
                    } else if c < -self.threshold {
                        "good"
                    } else {
                        "mut"
                    };
                    format!(r#" <span class="{class}">{c:+.2} %</span>"#)
                })
                .unwrap_or_default();
            let _ = write!(
                out,
                r#"<div class="card"><b>{}</b><br>{}{}{}</div>"#,
                esc(name.rsplit("::").next().unwrap_or(name)),
                fmt_short(last.value),
                delta,
                charts::line(points, self.threshold),
            );
        }
        if !current.is_empty() {
            out += "</div>";
        }
        Ok(out)
    }

    pub fn run(&self, id: i64, log_dir: &Path) -> Result<Option<String>> {
        let Some(run) = self.db.run(id)? else {
            return Ok(None);
        };
        let mut body = format!(
            r#"<h2>{what} · {sha}</h2><p>{title}</p><p class="mut">status <b>{status}</b> · queued {created}{started}{finished}</p>"#,
            what = what(&run),
            sha = sha_link(self.repo, &run.head_sha),
            title = esc(&run.title),
            status = esc(&run.status),
            created = day(run.created_at),
            started = run
                .started_at
                .map(|t| format!(" · started {}", day(t)))
                .unwrap_or_default(),
            finished = run
                .finished_at
                .map(|t| format!(" · finished {}", day(t)))
                .unwrap_or_default(),
        );
        if let Some(env) = &run.env {
            let _ = write!(
                body,
                r#"<p class="mut">{} · {} · {} · {}{}</p>"#,
                esc(&env.host),
                esc(&env.cpu),
                esc(&env.rustc),
                esc(&env.valgrind),
                env.pinned_cpu
                    .as_ref()
                    .map(|c| format!(" · pinned to cpu {}", esc(c)))
                    .unwrap_or_default()
            );
        }
        if let Some(e) = &run.error {
            let _ = write!(body, r#"<pre class="bad">{}</pre>"#, esc(e));
        }
        if run.status == "done" {
            let head = self.db.results(id, "head")?;
            match &run.base_sha {
                Some(base) => {
                    let base_results = self.db.results(id, "base")?;
                    let rows = compare::compare(&base_results, &head, self.threshold);
                    let _ = write!(
                        body,
                        "<h3>Against merge base {} — {}</h3>{}",
                        sha_link(self.repo, base),
                        esc(&compare::summary(&rows)),
                        comparison_table(&rows)
                    );
                }
                None => body += &metrics_table(&head),
            }
            body += &self.wall_clock(id, run.base_sha.is_some())?;
        }
        body += &log_section(&run, log_dir);
        Ok(Some(page(&format!("run {id}"), &body)))
    }

    fn wall_clock(&self, id: i64, has_base: bool) -> Result<String> {
        let head = self.db.wall(id, "head")?;
        let base = if has_base {
            self.db.wall(id, "base")?
        } else {
            Default::default()
        };
        if head.is_empty() && base.is_empty() {
            return Ok(String::new());
        }
        let mut names: Vec<&String> = head.keys().chain(base.keys()).collect();
        names.sort();
        names.dedup();
        let mut out = String::from(
            r#"<h3>Wall-clock times</h3><p class="mut">Criterion means of a single run. They depend on the machine and are not compared; use the instruction counts above for that.</p><table><tr><th>benchmark</th>"#,
        );
        if has_base {
            out += "<th>base</th>";
        }
        out += "<th>head</th></tr>";
        for n in names {
            let cell = |r: &crate::model::WallResults| {
                r.get(n)
                    .map(|w| {
                        format!(
                            "{} <span class=\"mut\">({} … {})</span>",
                            fmt_ns(w.mean_ns),
                            fmt_ns(w.lo_ns),
                            fmt_ns(w.hi_ns)
                        )
                    })
                    .unwrap_or_else(|| "–".into())
            };
            let _ = write!(out, "<tr><td>{}</td>", esc(n));
            if has_base {
                let _ = write!(out, "<td>{}</td>", cell(&base));
            }
            let _ = write!(out, "<td>{}</td></tr>", cell(&head));
        }
        out += "</table>";
        Ok(out)
    }
}

fn metrics_table(results: &Results) -> String {
    let mut out = String::from(
        "<h3>Results</h3><table><tr><th>benchmark</th><th>instructions</th><th>est. cycles</th><th>L1 hits</th><th>LL hits</th><th>RAM hits</th><th>heap bytes</th><th>allocations</th></tr>",
    );
    for (name, m) in results {
        let opt = |v: Option<u64>| v.map(fmt_count).unwrap_or_else(|| "–".into());
        let _ = write!(
            out,
            "<tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>",
            esc(name),
            fmt_count(m.instructions),
            fmt_count(m.estimated_cycles),
            fmt_count(m.l1_hits),
            fmt_count(m.ll_hits),
            fmt_count(m.ram_hits),
            opt(m.heap_bytes),
            opt(m.heap_blocks),
        );
    }
    out + "</table>"
}

fn comparison_table(rows: &[Row]) -> String {
    let mut out = String::from(
        "<table><tr><th>benchmark</th><th>base</th><th>head</th><th>change</th><th>heap bytes</th></tr>",
    );
    for r in rows {
        let class = match r.verdict {
            Verdict::Regression => "bad",
            Verdict::Improvement => "good",
            _ => "mut",
        };
        let cell = |m: &Option<crate::model::Metrics>| {
            m.map(|m| fmt_count(m.instructions))
                .unwrap_or_else(|| "–".into())
        };
        let change = match (r.change, r.verdict) {
            (Some(c), _) if c.is_finite() => format!("{c:+.2} %"),
            (Some(_), _) => "new work".into(),
            (None, Verdict::New) => "new".into(),
            _ => "removed".into(),
        };
        let heap = r
            .heap_change
            .filter(|c| c.is_finite())
            .map(|c| format!("{c:+.2} %"))
            .unwrap_or_default();
        let _ = write!(
            out,
            r#"<tr><td>{}</td><td>{}</td><td>{}</td><td class="{class}">{change}</td><td>{heap}</td></tr>"#,
            esc(&r.name),
            cell(&r.base),
            cell(&r.head),
        );
    }
    out + "</table>"
}

/// The log of a run. While the run is going the log is refreshed.
fn log_section(run: &RunInfo, log_dir: &Path) -> String {
    let live = matches!(run.status.as_str(), "running" | "queued");
    let text = log_tail(&log_dir.join(format!("{}.log", run.id)));
    if !live && text.is_empty() {
        return String::new();
    }
    let attrs = if live {
        format!(
            r#" hx-get="/fragments/log/{}" hx-trigger="every 2s" hx-swap="innerHTML""#,
            run.id
        )
    } else {
        String::new()
    };
    format!("<h3>Log</h3><pre id=\"log\"{attrs}>{}</pre>", esc(&text))
}

/// The last lines of a log file.
pub fn log_tail(path: &Path) -> String {
    let text = std::fs::read_to_string(path).unwrap_or_default();
    let lines: Vec<&str> = text.lines().rev().take(200).collect();
    lines.into_iter().rev().collect::<Vec<_>>().join("\n")
}
