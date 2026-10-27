//! SQLite storage for runs and their results.

use crate::compare::{self, Row};
use crate::model::{EnvInfo, Measured, Metric, Metrics, Results, WallClock, WallResults, now};
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

/// A run as shown in lists.
#[derive(Debug, Clone, Serialize)]
pub struct RunInfo {
    pub id: i64,
    pub kind: String,
    pub pr: Option<u64>,
    pub title: String,
    pub head_sha: String,
    pub base_sha: Option<String>,
    pub status: String,
    pub created_at: i64,
    pub started_at: Option<i64>,
    pub finished_at: Option<i64>,
    pub error: Option<String>,
    pub env: Option<EnvInfo>,
}

/// One commit of `main` in the history of a benchmark.
#[derive(Debug, Clone, Serialize)]
pub struct Point {
    pub run: i64,
    pub sha: String,
    pub time: i64,
    pub value: u64,
}

#[derive(Serialize)]
pub struct PrRun {
    pub info: RunInfo,
    pub rows: Vec<Row>,
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
    instructions INTEGER NOT NULL,
    estimated_cycles INTEGER NOT NULL,
    l1_hits INTEGER NOT NULL,
    ll_hits INTEGER NOT NULL,
    ram_hits INTEGER NOT NULL,
    heap_bytes INTEGER,
    heap_blocks INTEGER,
    PRIMARY KEY (run_id, role, bench)
);
CREATE TABLE IF NOT EXISTS wallclock (
    run_id INTEGER NOT NULL REFERENCES runs(id) ON DELETE CASCADE,
    role TEXT NOT NULL,
    bench TEXT NOT NULL,
    mean_ns REAL NOT NULL,
    lo_ns REAL NOT NULL,
    hi_ns REAL NOT NULL,
    PRIMARY KEY (run_id, role, bench)
);
CREATE INDEX IF NOT EXISTS runs_head ON runs(head_sha);
";

const RUN_COLUMNS: &str = "id, kind, pr, title, head_sha, base_sha, status, created_at, started_at, finished_at, error, env";

fn run_info(r: &rusqlite::Row) -> rusqlite::Result<RunInfo> {
    let env: Option<String> = r.get(11)?;
    Ok(RunInfo {
        id: r.get(0)?,
        kind: r.get(1)?,
        pr: r.get(2)?,
        title: r.get(3)?,
        head_sha: r.get(4)?,
        base_sha: r.get(5)?,
        status: r.get(6)?,
        created_at: r.get(7)?,
        started_at: r.get(8)?,
        finished_at: r.get(9)?,
        error: r.get(10)?,
        env: env.and_then(|e| serde_json::from_str(&e).ok()),
    })
}

impl Db {
    pub fn open(path: &Path) -> Result<Self> {
        let conn = Connection::open(path).with_context(|| format!("opening {}", path.display()))?;
        conn.pragma_update(None, "journal_mode", "WAL")?;
        conn.pragma_update(None, "foreign_keys", "ON")?;
        conn.busy_timeout(std::time::Duration::from_secs(10))?;
        // Databases of the criterion-based runner have a `results` table with wall-clock
        // columns. Those numbers are not comparable with instruction counts, so the table is
        // kept under another name and not shown anywhere.
        let legacy: bool = conn
            .prepare("SELECT 1 FROM pragma_table_info('results') WHERE name='mean_ns'")?
            .exists([])?;
        if legacy {
            conn.execute_batch("ALTER TABLE results RENAME TO legacy_criterion_results;")?;
        }
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

    /// Removes a run from the queue. Returns whether it was queued.
    pub fn discard(&self, id: i64) -> Result<bool> {
        let n = self.0.execute(
            "UPDATE runs SET status='cancelled', finished_at=?2, error='discarded from the queue'
             WHERE id=?1 AND status='queued'",
            params![id, now()],
        )?;
        Ok(n > 0)
    }

    /// Removes everything that waits in the queue. Returns the number of runs.
    pub fn discard_all(&self) -> Result<usize> {
        Ok(self.0.execute(
            "UPDATE runs SET status='cancelled', finished_at=?1, error='discarded from the queue'
             WHERE status='queued'",
            [now()],
        )?)
    }

    /// Records that a running run was stopped on request.
    pub fn mark_cancelled(&self, id: i64) -> Result<()> {
        self.0.execute(
            "UPDATE runs SET status='cancelled', finished_at=?2, error='cancelled while running' WHERE id=?1",
            params![id, now()],
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
        measured: &BTreeMap<String, Measured>,
    ) -> Result<()> {
        let tx = self.0.unchecked_transaction()?;
        for (role, m) in measured {
            for (bench, e) in &m.results {
                tx.execute(
                    "INSERT OR REPLACE INTO results VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10)",
                    params![
                        id,
                        role,
                        bench,
                        e.instructions,
                        e.estimated_cycles,
                        e.l1_hits,
                        e.ll_hits,
                        e.ram_hits,
                        e.heap_bytes,
                        e.heap_blocks
                    ],
                )?;
            }
            for (bench, w) in &m.wall {
                tx.execute(
                    "INSERT OR REPLACE INTO wallclock VALUES (?1,?2,?3,?4,?5,?6)",
                    params![id, role, bench, w.mean_ns, w.lo_ns, w.hi_ns],
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
            "SELECT bench, instructions, estimated_cycles, l1_hits, ll_hits, ram_hits, heap_bytes, heap_blocks
             FROM results WHERE run_id=?1 AND role=?2",
        )?;
        let rows = stmt.query_map(params![run, role], |r| {
            Ok((
                r.get::<_, String>(0)?,
                Metrics {
                    instructions: r.get(1)?,
                    estimated_cycles: r.get(2)?,
                    l1_hits: r.get(3)?,
                    ll_hits: r.get(4)?,
                    ram_hits: r.get(5)?,
                    heap_bytes: r.get(6)?,
                    heap_blocks: r.get(7)?,
                },
            ))
        })?;
        Ok(rows.collect::<rusqlite::Result<_>>()?)
    }

    pub fn wall(&self, run: i64, role: &str) -> Result<WallResults> {
        let mut stmt = self.0.prepare(
            "SELECT bench, mean_ns, lo_ns, hi_ns FROM wallclock WHERE run_id=?1 AND role=?2",
        )?;
        let rows = stmt.query_map(params![run, role], |r| {
            Ok((
                r.get::<_, String>(0)?,
                WallClock {
                    mean_ns: r.get(1)?,
                    lo_ns: r.get(2)?,
                    hi_ns: r.get(3)?,
                },
            ))
        })?;
        Ok(rows.collect::<rusqlite::Result<_>>()?)
    }

    /// The measurement of a commit of `main` that was already benchmarked, so that a pull
    /// request does not measure its merge base again.
    pub fn main_measurement(&self, sha: &str) -> Result<Option<Measured>> {
        let id: Option<i64> = self
            .0
            .query_row(
                "SELECT id FROM runs WHERE kind='main' AND head_sha=?1 AND status='done'
                 ORDER BY id DESC LIMIT 1",
                [sha],
                |r| r.get(0),
            )
            .optional()?;
        id.map(|id| {
            Ok(Measured {
                results: self.results(id, "head")?,
                wall: self.wall(id, "head")?,
            })
        })
        .transpose()
    }

    pub fn run(&self, id: i64) -> Result<Option<RunInfo>> {
        Ok(self
            .0
            .query_row(
                &format!("SELECT {RUN_COLUMNS} FROM runs WHERE id=?1"),
                [id],
                run_info,
            )
            .optional()?)
    }

    /// Queued and running runs, the running one first.
    pub fn queue(&self) -> Result<Vec<RunInfo>> {
        let mut stmt = self.0.prepare(&format!(
            "SELECT {RUN_COLUMNS} FROM runs WHERE status IN ('queued','running')
             ORDER BY (status='running') DESC, (kind='pr') DESC, id"
        ))?;
        Ok(stmt
            .query_map([], run_info)?
            .collect::<rusqlite::Result<_>>()?)
    }

    /// The most recent runs of `main`, newest first.
    pub fn recent_main_runs(&self, limit: usize) -> Result<Vec<RunInfo>> {
        let mut stmt = self.0.prepare(&format!(
            "SELECT {RUN_COLUMNS} FROM runs WHERE kind='main' AND status != 'queued'
             ORDER BY id DESC LIMIT ?1"
        ))?;
        Ok(stmt
            .query_map([limit], run_info)?
            .collect::<rusqlite::Result<_>>()?)
    }

    /// Value of `metric` of every benchmark at every finished commit of `main`, oldest first,
    /// limited to the last `history` commits.
    pub fn history(&self, metric: Metric, history: usize) -> Result<BTreeMap<String, Vec<Point>>> {
        let column = match metric {
            Metric::Instructions => "instructions",
            Metric::EstimatedCycles => "estimated_cycles",
            Metric::HeapBytes => "heap_bytes",
            Metric::HeapBlocks => "heap_blocks",
        };
        let mut stmt = self.0.prepare(&format!(
            "SELECT r.bench, runs.id, runs.head_sha, COALESCE(runs.finished_at, runs.created_at), r.{column}
             FROM results r JOIN runs ON runs.id = r.run_id
             WHERE runs.kind='main' AND runs.status='done' AND r.role='head' AND r.{column} IS NOT NULL
               AND runs.id IN (SELECT id FROM runs WHERE kind='main' AND status='done' ORDER BY id DESC LIMIT ?1)
             ORDER BY runs.id"
        ))?;
        let rows = stmt.query_map([history], |r| {
            Ok((
                r.get::<_, String>(0)?,
                Point {
                    run: r.get(1)?,
                    sha: r.get(2)?,
                    time: r.get(3)?,
                    value: r.get(4)?,
                },
            ))
        })?;
        let mut benches: BTreeMap<String, Vec<Point>> = BTreeMap::new();
        for row in rows {
            let (bench, point) = row?;
            benches.entry(bench).or_default().push(point);
        }
        Ok(benches)
    }

    /// The latest pull request runs with their comparison, newest first.
    pub fn pull_requests(&self, threshold: f64) -> Result<Vec<PrRun>> {
        let mut stmt = self.0.prepare(&format!(
            "SELECT {RUN_COLUMNS} FROM runs WHERE kind='pr' AND status NOT IN ('cancelled','queued')
             ORDER BY id DESC LIMIT 30"
        ))?;
        let infos = stmt
            .query_map([], run_info)?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        infos
            .into_iter()
            .map(|info| {
                let rows = if info.status == "done" {
                    compare::compare(
                        &self.results(info.id, "base")?,
                        &self.results(info.id, "head")?,
                        threshold,
                    )
                } else {
                    Vec::new()
                };
                Ok(PrRun { info, rows })
            })
            .collect()
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

    fn main_run(sha: &str) -> NewRun {
        NewRun {
            kind: "main".into(),
            pr: None,
            title: "t".into(),
            head_sha: sha.into(),
        }
    }

    fn metrics(ir: u64) -> Metrics {
        Metrics {
            instructions: ir,
            estimated_cycles: 2 * ir,
            l1_hits: 1,
            ll_hits: 2,
            ram_hits: 3,
            heap_bytes: Some(10),
            heap_blocks: None,
        }
    }

    fn measured(ir: u64) -> BTreeMap<String, Measured> {
        BTreeMap::from([(
            "head".to_string(),
            Measured {
                results: Results::from([("x".to_string(), metrics(ir))]),
                wall: WallResults::from([(
                    "w".to_string(),
                    WallClock {
                        mean_ns: 1.0,
                        lo_ns: 0.5,
                        hi_ns: 2.0,
                    },
                )]),
            },
        )])
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
        db.finish(id, None, &EnvInfo::default(), &measured(5))
            .unwrap();
        assert_eq!(db.results(id, "head").unwrap()["x"], metrics(5));
        assert_eq!(db.wall(id, "head").unwrap()["w"].mean_ns, 1.0);
        assert_eq!(db.pull_requests(1.0).unwrap().len(), 1);
    }

    #[test]
    fn discarding_only_affects_queued_runs() {
        let db = db();
        let a = db.enqueue(&main_run("a")).unwrap().unwrap();
        let b = db.enqueue(&main_run("b")).unwrap().unwrap();
        let running = db.claim().unwrap().unwrap().id;
        assert_eq!(running, a);
        assert!(
            !db.discard(a).unwrap(),
            "a running run is cancelled, not discarded"
        );
        assert!(db.discard(b).unwrap());
        assert!(db.queue().unwrap().iter().all(|r| r.id == a));
        // a discarded commit can be queued again
        assert!(db.enqueue(&main_run("b")).unwrap().is_some());
        db.mark_cancelled(a).unwrap();
        assert_eq!(db.run(a).unwrap().unwrap().status, "cancelled");
    }

    #[test]
    fn history_lists_commits_oldest_first() {
        let db = db();
        for (sha, ir) in [("a", 10), ("b", 20), ("c", 30)] {
            let id = db.enqueue(&main_run(sha)).unwrap().unwrap();
            db.claim().unwrap();
            db.finish(id, None, &EnvInfo::default(), &measured(ir))
                .unwrap();
        }
        let h = db.history(Metric::Instructions, 2).unwrap();
        let values: Vec<u64> = h["x"].iter().map(|p| p.value).collect();
        assert_eq!(values, vec![20, 30]);
        // heap blocks were not measured
        assert!(db.history(Metric::HeapBlocks, 10).unwrap().is_empty());
        assert!(db.main_measurement("b").unwrap().is_some());
        assert!(db.main_measurement("zzz").unwrap().is_none());
    }

    #[test]
    fn criterion_results_are_set_aside() {
        let dir = std::env::temp_dir().join(format!("ab-db-{}.sqlite", std::process::id()));
        {
            let conn = Connection::open(&dir).unwrap();
            conn.execute_batch(
                "CREATE TABLE results (run_id INTEGER, role TEXT, bench TEXT, mean_ns REAL);",
            )
            .unwrap();
        }
        let db = Db::open(&dir).unwrap();
        assert!(db.results(1, "head").unwrap().is_empty());
        drop(db);
        let _ = std::fs::remove_file(&dir);
    }
}
