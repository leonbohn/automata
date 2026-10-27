//! Comparing two sets of results and presenting the outcome.

use crate::model::{Estimate, Results, fmt_ns};
use serde::Serialize;

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
    pub base: Option<Estimate>,
    pub head: Option<Estimate>,
    /// Relative change in percent, positive is slower.
    pub change: Option<f64>,
    pub verdict: Verdict,
}

/// A change counts if it exceeds `threshold` percent and the ranges of the two measurements
/// (which span all rounds) do not overlap.
pub fn compare(base: &Results, head: &Results, threshold: f64) -> Vec<Row> {
    let mut names: Vec<&String> = base.keys().chain(head.keys()).collect();
    names.sort();
    names.dedup();
    let mut rows: Vec<Row> = names
        .into_iter()
        .map(|name| {
            let (b, h) = (base.get(name).copied(), head.get(name).copied());
            let (change, verdict) = match (b, h) {
                (Some(b), Some(h)) => {
                    let change = (h.mean_ns / b.mean_ns - 1.0) * 100.0;
                    let verdict = if change > threshold && h.min_ns > b.max_ns {
                        Verdict::Regression
                    } else if change < -threshold && h.max_ns < b.min_ns {
                        Verdict::Improvement
                    } else {
                        Verdict::Unchanged
                    };
                    (Some(change), verdict)
                }
                (None, Some(_)) => (None, Verdict::New),
                _ => (None, Verdict::Removed),
            };
            Row {
                name: name.clone(),
                base: b,
                head: h,
                change,
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

fn cell(e: &Option<Estimate>) -> String {
    e.map(|e| fmt_ns(e.mean_ns)).unwrap_or_else(|| "–".into())
}

/// Renders the rows as a Markdown table, without a heading.
pub fn table(rows: &[Row]) -> String {
    let mut out = String::from("| benchmark | base | head | change | |\n|---|--:|--:|--:|:-:|\n");
    for row in rows {
        let (change, mark) = match (row.change, row.verdict) {
            (Some(c), Verdict::Regression) => (format!("{c:+.1} %"), "🔴"),
            (Some(c), Verdict::Improvement) => (format!("{c:+.1} %"), "🟢"),
            (Some(c), _) => (format!("{c:+.1} %"), ""),
            (None, Verdict::New) => ("new".into(), "🆕"),
            (None, _) => ("removed".into(), ""),
        };
        out += &format!(
            "| `{}` | {} | {} | {change} | {mark} |\n",
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

    fn est(mean: f64, min: f64, max: f64) -> Estimate {
        Estimate {
            mean_ns: mean,
            min_ns: min,
            max_ns: max,
            median_ns: mean,
            stddev_ns: 0.0,
            rounds: 3,
        }
    }

    #[test]
    fn classifies() {
        let base = Results::from([
            ("slow".into(), est(100.0, 95.0, 105.0)),
            ("noisy".into(), est(100.0, 80.0, 130.0)),
            ("fast".into(), est(100.0, 95.0, 105.0)),
            ("same".into(), est(100.0, 95.0, 105.0)),
            ("gone".into(), est(1.0, 1.0, 1.0)),
        ]);
        let head = Results::from([
            ("slow".into(), est(150.0, 140.0, 160.0)),
            ("noisy".into(), est(150.0, 120.0, 170.0)),
            ("fast".into(), est(50.0, 45.0, 55.0)),
            ("same".into(), est(103.0, 98.0, 108.0)),
            ("fresh".into(), est(1.0, 1.0, 1.0)),
        ]);
        let v: Vec<_> = compare(&base, &head, 10.0)
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
                ("noisy".to_string(), Verdict::Unchanged),
                ("same".to_string(), Verdict::Unchanged),
            ]
        );
    }
}
