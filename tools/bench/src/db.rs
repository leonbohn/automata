//! SQLite storage for runs and their results.

use crate::compare::{self, Row};
use crate::model::{EnvInfo, Estimate, Results, now};
use anyhow::{Context, Result};
use rusqlite::{Connection, OptionalExtension, params};
use serde::Serialize;
use std::collections::BTreeMap;
use std::path::Path;

pub struct Db(Connection);

#[derive(Debug, Clone)]
pub struct NewRun {
    pub kind: String,
    pub pr: Option<u64>,
    pub title: String,
    pub head_sha: String,
}

#[derive(Debug, Clone)]
pub struct Run {
    pub id: i64,
    pub kind: String,
    pub pr: Option<u64>,
    pub head_sha: String,
}

#[derive(Serialize)]
pub struct Point {
    pub run: i64,
    pub sha: String,
    pub time: i64,
    pub mean: f64,
    pub min: f64,
    pub max: f64,
}

#[derive(Serialize)]
pub struct PrRun {
    pub id: i64,
    pub pr: u64,
    pub title: String,
    pub head: String,
    pub base: Option<String>,
    pub status: String,
    pub time: i64,
    pub error: Option<String>,
    pub rows: Vec<Row>,
}

#[derive(Serialize)]
pub struct DashboardData {
    pub generated: i64,
    pub benches: BTreeMap<String, Vec<Point>>,
    pub prs: Vec<PrRun>,
    pub queue: Vec<String>,
    pub env: Option<EnvInfo>,
}

const SCHEMA: &str = "
CREATE TABLE IF NOT EXISTS runs (
    id INTEGER PRIMARY KEY,
    kind TEXT NOT NULL,             -- 'main' or 'pr'
    pr INTEGER,
    title TEXT NOT NULL DEFAULT '',
    head_sha TEXT NOT NULL,
    base_sha TEXT,
    status TEXT NOT NULL,           -- queued, running, done, failed, cancelled
    created_at INTEGER NOT NULL,
    started_at INTEGER,
    finished_at INTEGER,
    error TEXT,
    env TEXT
);
CREATE TABLE IF NOT EXISTS results (
    run_id INTEGER NOT NULL REFERENCES runs(id) ON DELETE CASCADE,
    role TEXT NOT NULL,             -- 'head' or 'base'
    bench TEXT NOT NULL,
    mean_ns REAL NOT NULL,
    min_ns REAL NOT NULL,
    max_ns REAL NOT NULL,
    median_ns REAL NOT NULL,
    stddev_ns REAL NOT NULL,
    rounds INTEGER NOT NULL,
    PRIMARY KEY (run_id, role, bench)
);
CREATE INDEX IF NOT EXISTS runs_head ON runs(head_sha);
";

impl Db {
    pub fn open(path: &Path) -> Result<Self> {
        let conn = Connection::open(path).with_context(|| format!("opening {}", path.display()))?;
        conn.pragma_update(None, "journal_mode", "WAL")?;
        conn.pragma_update(None, "foreign_keys", "ON")?;
        conn.busy_timeout(std::time::Duration::from_secs(10))?;
        conn.execute_batch(SCHEMA)?;
        Ok(Self(conn))
    }

    /// Runs interrupted by a restart are queued again.
    pub fn recover(&self) -> Result<()> {
        self.0
            .execute("UPDATE runs SET status='queued' WHERE status='running'", [])?;
        Ok(())
    }

    /// Queues a run. A queued run for the same pull request is replaced, and a main commit that
    /// already has a (queued, running or finished) run is not queued again. Returns `None` then.
    pub fn enqueue(&self, run: &NewRun) -> Result<Option<i64>> {
        if run.kind == "pr" {
            self.0.execute(
                "UPDATE runs SET status='cancelled' WHERE kind='pr' AND pr=?1 AND status='queued'",
                [run.pr],
            )?;
            let dup: Option<i64> = self
                .0
                .query_row(
                    "SELECT id FROM runs WHERE kind='pr' AND pr=?1 AND head_sha=?2
                     AND status IN ('queued','running','done')",
                    params![run.pr, run.head_sha],
                    |r| r.get(0),
                )
                .optional()?;
            if dup.is_some() {
                return Ok(None);
            }
        } else {
            let dup: Option<i64> = self
                .0
                .query_row(
                    "SELECT id FROM runs WHERE kind='main' AND head_sha=?1
                     AND status IN ('queued','running','done')",
                    [&run.head_sha],
                    |r| r.get(0),
                )
                .optional()?;
            if dup.is_some() {
                return Ok(None);
            }
        }
        self.0.execute(
            "INSERT INTO runs (kind, pr, title, head_sha, status, created_at)
             VALUES (?1, ?2, ?3, ?4, 'queued', ?5)",
            params![run.kind, run.pr, run.title, run.head_sha, now()],
        )?;
        Ok(Some(self.0.last_insert_rowid()))
    }

    pub fn cancel_pr(&self, pr: u64) -> Result<()> {
        self.0.execute(
            "UPDATE runs SET status='cancelled' WHERE kind='pr' AND pr=?1 AND status='queued'",
            [pr],
        )?;
        Ok(())
    }

    /// Takes the oldest queued run, marking it as running. Pull requests go first.
    pub fn claim(&self) -> Result<Option<Run>> {
        let run = self
            .0
            .query_row(
                "SELECT id, kind, pr, head_sha FROM runs WHERE status='queued'
                 ORDER BY (kind='pr') DESC, id LIMIT 1",
                [],
                |r| {
                    Ok(Run {
                        id: r.get(0)?,
                        kind: r.get(1)?,
                        pr: r.get(2)?,
                        head_sha: r.get(3)?,
                    })
                },
            )
            .optional()?;
        if let Some(run) = &run {
            self.0.execute(
                "UPDATE runs SET status='running', started_at=?2 WHERE id=?1",
                params![run.id, now()],
            )?;
        }
        Ok(run)
    }

    pub fn finish(
        &self,
        id: i64,
        base_sha: Option<&str>,
        env: &EnvInfo,
        results: &BTreeMap<String, Results>,
    ) -> Result<()> {
        let tx = self.0.unchecked_transaction()?;
        for (role, results) in results {
            for (bench, e) in results {
                tx.execute(
                    "INSERT OR REPLACE INTO results VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9)",
                    params![
                        id,
                        role,
                        bench,
                        e.mean_ns,
                        e.min_ns,
                        e.max_ns,
                        e.median_ns,
                        e.stddev_ns,
                        e.rounds
                    ],
                )?;
            }
        }
        tx.execute(
            "UPDATE runs SET status='done', finished_at=?2, base_sha=?3, env=?4, error=NULL WHERE id=?1",
            params![id, now(), base_sha, serde_json::to_string(env)?],
        )?;
        tx.commit()?;
        Ok(())
    }

    pub fn fail(&self, id: i64, error: &str) -> Result<()> {
        self.0.execute(
            "UPDATE runs SET status='failed', finished_at=?2, error=?3 WHERE id=?1",
            params![id, now(), error],
        )?;
        Ok(())
    }

    pub fn results(&self, run: i64, role: &str) -> Result<Results> {
        let mut stmt = self.0.prepare(
            "SELECT bench, mean_ns, min_ns, max_ns, median_ns, stddev_ns, rounds
             FROM results WHERE run_id=?1 AND role=?2",
        )?;
        let rows = stmt.query_map(params![run, role], |r| {
            Ok((
                r.get::<_, String>(0)?,
                Estimate {
                    mean_ns: r.get(1)?,
                    min_ns: r.get(2)?,
                    max_ns: r.get(3)?,
                    median_ns: r.get(4)?,
                    stddev_ns: r.get(5)?,
                    rounds: r.get(6)?,
                },
            ))
        })?;
        Ok(rows.collect::<rusqlite::Result<_>>()?)
    }

    pub fn dashboard(&self, threshold: f64, history: usize) -> Result<DashboardData> {
        let mut benches: BTreeMap<String, Vec<Point>> = BTreeMap::new();
        let mut stmt = self.0.prepare(
            "SELECT r.bench, runs.id, runs.head_sha, runs.finished_at, r.mean_ns, r.min_ns, r.max_ns
             FROM results r JOIN runs ON runs.id = r.run_id
             WHERE runs.kind='main' AND runs.status='done' AND r.role='head'
             ORDER BY runs.finished_at, runs.id",
        )?;
        let rows = stmt.query_map([], |r| {
            Ok((
                r.get::<_, String>(0)?,
                Point {
                    run: r.get(1)?,
                    sha: r.get(2)?,
                    time: r.get(3)?,
                    mean: r.get(4)?,
                    min: r.get(5)?,
                    max: r.get(6)?,
                },
            ))
        })?;
        for row in rows {
            let (bench, point) = row?;
            benches.entry(bench).or_default().push(point);
        }
        for points in benches.values_mut() {
            let excess = points.len().saturating_sub(history);
            points.drain(..excess);
        }

        let mut prs = Vec::new();
        let mut stmt = self.0.prepare(
            "SELECT id, pr, title, head_sha, base_sha, status, COALESCE(finished_at, created_at), error
             FROM runs WHERE kind='pr' AND status != 'cancelled' ORDER BY id DESC LIMIT 30",
        )?;
        let rows = stmt.query_map([], |r| {
            Ok((
                r.get::<_, i64>(0)?,
                r.get::<_, u64>(1)?,
                r.get::<_, String>(2)?,
                r.get::<_, String>(3)?,
                r.get::<_, Option<String>>(4)?,
                r.get::<_, String>(5)?,
                r.get::<_, i64>(6)?,
                r.get::<_, Option<String>>(7)?,
            ))
        })?;
        for row in rows {
            let (id, pr, title, head, base, status, time, error) = row?;
            let rows = if status == "done" {
                compare::compare(
                    &self.results(id, "base")?,
                    &self.results(id, "head")?,
                    threshold,
                )
            } else {
                Vec::new()
            };
            prs.push(PrRun {
                id,
                pr,
                title,
                head,
                base,
                status,
                time,
                error,
                rows,
            });
        }

        let mut stmt = self.0.prepare(
            "SELECT kind, pr, head_sha, status FROM runs WHERE status IN ('queued','running') ORDER BY id",
        )?;
        let queue = stmt
            .query_map([], |r| {
                let pr: Option<u64> = r.get(1)?;
                let sha: String = r.get(2)?;
                let what = pr
                    .map(|p| format!("PR #{p}"))
                    .unwrap_or_else(|| "main".into());
                Ok(format!(
                    "{what} @ {} ({})",
                    &sha[..sha.len().min(8)],
                    r.get::<_, String>(3)?
                ))
            })?
            .collect::<rusqlite::Result<_>>()?;

        let env: Option<String> = self
            .0
            .query_row(
                "SELECT env FROM runs WHERE status='done' ORDER BY finished_at DESC LIMIT 1",
                [],
                |r| r.get(0),
            )
            .optional()?
            .flatten();
        Ok(DashboardData {
            generated: now(),
            benches,
            prs,
            queue,
            env: env.and_then(|e| serde_json::from_str(&e).ok()),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn db() -> Db {
        Db::open(Path::new(":memory:")).unwrap()
    }

    fn pr(n: u64, sha: &str) -> NewRun {
        NewRun {
            kind: "pr".into(),
            pr: Some(n),
            title: "t".into(),
            head_sha: sha.into(),
        }
    }

    #[test]
    fn queue_coalesces_pull_requests() {
        let db = db();
        let first = db.enqueue(&pr(1, "aaa")).unwrap().unwrap();
        let second = db.enqueue(&pr(1, "bbb")).unwrap().unwrap();
        assert_ne!(first, second);
        // the older queued run was replaced, so only the newest gets claimed
        assert_eq!(db.claim().unwrap().unwrap().id, second);
        assert!(db.claim().unwrap().is_none());
        // the same commit is not queued twice
        assert!(db.enqueue(&pr(1, "bbb")).unwrap().is_none());
    }

    #[test]
    fn stores_and_loads_results() {
        let db = db();
        let id = db.enqueue(&pr(2, "ccc")).unwrap().unwrap();
        db.claim().unwrap();
        let e = Estimate {
            mean_ns: 1.0,
            min_ns: 0.5,
            max_ns: 2.0,
            median_ns: 1.0,
            stddev_ns: 0.1,
            rounds: 3,
        };
        let results = BTreeMap::from([("head".to_string(), Results::from([("x".to_string(), e)]))]);
        db.finish(id, None, &EnvInfo::default(), &results).unwrap();
        assert_eq!(db.results(id, "head").unwrap()["x"], e);
        assert_eq!(db.dashboard(10.0, 100).unwrap().prs.len(), 1);
    }
}
