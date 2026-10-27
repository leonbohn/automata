//! Comparing two sets of results and presenting the outcome.
//!
//! Instruction counts are exact, so there is no statistics here: a benchmark changed if its
//! instruction count differs by more than the threshold.

use crate::model::{Metrics, Results, fmt_short};
use serde::Serialize;

/// Below this many instructions of difference, a change is startup noise whatever its size in
/// percent.
const MIN_ABSOLUTE_CHANGE: u64 = 1_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Verdict {
    Regression,
    Improvement,
    Unchanged,
    New,
    Removed,
}

#[derive(Debug, Clone, Serialize)]
pub struct Row {
    pub name: String,
    pub base: Option<Metrics>,
    pub head: Option<Metrics>,
    /// Relative change of the instruction count in percent, positive is worse.
    pub change: Option<f64>,
    /// Relative change of the heap bytes in percent, if both sides were measured with DHAT.
    pub heap_change: Option<f64>,
    pub verdict: Verdict,
}

pub fn relative_change(base: u64, head: u64) -> f64 {
    if base == 0 {
        return if head == 0 { 0.0 } else { f64::INFINITY };
    }
    (head as f64 / base as f64 - 1.0) * 100.0
}

pub fn compare(base: &Results, head: &Results, threshold: f64) -> Vec<Row> {
    let mut names: Vec<&String> = base.keys().chain(head.keys()).collect();
    names.sort();
    names.dedup();
    let mut rows: Vec<Row> = names
        .into_iter()
        .map(|name| {
            let (b, h) = (base.get(name).copied(), head.get(name).copied());
            let (change, heap_change, verdict) = match (b, h) {
                (Some(b), Some(h)) => {
                    let change = relative_change(b.instructions, h.instructions);
                    let big = b.instructions.abs_diff(h.instructions) >= MIN_ABSOLUTE_CHANGE;
                    let verdict = if big && change > threshold {
                        Verdict::Regression
                    } else if big && change < -threshold {
                        Verdict::Improvement
                    } else {
                        Verdict::Unchanged
                    };
                    let heap = b
                        .heap_bytes
                        .zip(h.heap_bytes)
                        .map(|(b, h)| relative_change(b, h));
                    (Some(change), heap, verdict)
                }
                (None, Some(_)) => (None, None, Verdict::New),
                _ => (None, None, Verdict::Removed),
            };
            Row {
                name: name.clone(),
                base: b,
                head: h,
                change,
                heap_change,
                verdict,
            }
        })
        .collect();
    let rank = |r: &Row| match r.verdict {
        Verdict::Regression => 0,
        Verdict::Improvement => 1,
        Verdict::New => 2,
        Verdict::Removed => 3,
        Verdict::Unchanged => 4,
    };
    rows.sort_by(|a, b| rank(a).cmp(&rank(b)).then(a.name.cmp(&b.name)));
    rows
}

pub fn count(rows: &[Row], verdict: Verdict) -> usize {
    rows.iter().filter(|r| r.verdict == verdict).count()
}

pub fn summary(rows: &[Row]) -> String {
    format!(
        "{} regressions, {} improvements, {} unchanged, {} new",
        count(rows, Verdict::Regression),
        count(rows, Verdict::Improvement),
        count(rows, Verdict::Unchanged),
        count(rows, Verdict::New),
    )
}

fn cell(m: &Option<Metrics>) -> String {
    m.map(|m| fmt_short(m.instructions))
        .unwrap_or_else(|| "–".into())
}

fn percent(change: f64) -> String {
    if change.is_infinite() {
        "new work".into()
    } else {
        format!("{change:+.2} %")
    }
}

/// Renders the rows as a Markdown table, without a heading.
pub fn table(rows: &[Row]) -> String {
    let mut out = String::from(
        "| benchmark | base | head | change | heap bytes | |\n|---|--:|--:|--:|--:|:-:|\n",
    );
    for row in rows {
        let (change, mark) = match (row.change, row.verdict) {
            (Some(c), Verdict::Regression) => (percent(c), "🔴"),
            (Some(c), Verdict::Improvement) => (percent(c), "🟢"),
            (Some(c), _) => (percent(c), ""),
            (None, Verdict::New) => ("new".into(), "🆕"),
            (None, _) => ("removed".into(), ""),
        };
        let heap = row.heap_change.map(percent).unwrap_or_default();
        out += &format!(
            "| `{}` | {} | {} | {change} | {heap} | {mark} |\n",
            row.name,
            cell(&row.base),
            cell(&row.head)
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    pub fn metrics(ir: u64) -> Metrics {
        Metrics {
            instructions: ir,
            estimated_cycles: ir * 2,
            l1_hits: 0,
            ll_hits: 0,
            ram_hits: 0,
            heap_bytes: None,
            heap_blocks: None,
        }
    }

    #[test]
    fn classifies() {
        let base = Results::from([
            ("slow".into(), metrics(1_000_000)),
            ("fast".into(), metrics(1_000_000)),
            ("same".into(), metrics(1_000_000)),
            ("tiny".into(), metrics(100)),
            ("gone".into(), metrics(1)),
        ]);
        let head = Results::from([
            ("slow".into(), metrics(1_020_000)),
            ("fast".into(), metrics(900_000)),
            ("same".into(), metrics(1_004_000)),
            ("tiny".into(), metrics(300)),
            ("fresh".into(), metrics(1)),
        ]);
        let v: Vec<_> = compare(&base, &head, 1.0)
            .into_iter()
            .map(|r| (r.name, r.verdict))
            .collect();
        assert_eq!(
            v,
            vec![
                ("slow".to_string(), Verdict::Regression),
                ("fast".to_string(), Verdict::Improvement),
                ("fresh".to_string(), Verdict::New),
                ("gone".to_string(), Verdict::Removed),
                ("same".to_string(), Verdict::Unchanged),
                ("tiny".to_string(), Verdict::Unchanged),
            ]
        );
    }

    #[test]
    fn heap_change_needs_both_sides() {
        let mut b = metrics(10_000);
        let mut h = metrics(10_000);
        b.heap_bytes = Some(100);
        h.heap_bytes = Some(150);
        let rows = compare(
            &Results::from([("x".into(), b)]),
            &Results::from([("x".into(), h)]),
            1.0,
        );
        assert_eq!(rows[0].heap_change, Some(50.0));
    }
}
