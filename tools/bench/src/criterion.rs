//! Reads the result files criterion leaves in `target/criterion`.

use crate::model::{Estimate, Results};
use anyhow::{Context, Result};
use serde::Deserialize;
use std::collections::BTreeMap;
use std::path::Path;

#[derive(Debug, Clone, Copy)]
pub struct Sample {
    pub mean: f64,
    pub lo: f64,
    pub hi: f64,
    pub median: f64,
    pub stddev: f64,
}

#[derive(Deserialize)]
struct BenchmarkJson {
    full_id: String,
}

#[derive(Deserialize)]
struct Interval {
    lower_bound: f64,
    upper_bound: f64,
}

#[derive(Deserialize)]
struct Stat {
    confidence_interval: Interval,
    point_estimate: f64,
}

#[derive(Deserialize)]
struct EstimatesJson {
    mean: Stat,
    median: Stat,
    std_dev: Stat,
}

/// Collects every benchmark below `dir` (a `target/criterion` directory) that has a `new` run.
pub fn collect(dir: &Path) -> Result<BTreeMap<String, Sample>> {
    let mut out = BTreeMap::new();
    walk(dir, &mut out)?;
    Ok(out)
}

fn walk(dir: &Path, out: &mut BTreeMap<String, Sample>) -> Result<()> {
    let new = dir.join("new");
    if new.join("benchmark.json").is_file() && new.join("estimates.json").is_file() {
        let id: BenchmarkJson = read(&new.join("benchmark.json"))?;
        let est: EstimatesJson = read(&new.join("estimates.json"))?;
        out.insert(
            id.full_id,
            Sample {
                mean: est.mean.point_estimate,
                lo: est.mean.confidence_interval.lower_bound,
                hi: est.mean.confidence_interval.upper_bound,
                median: est.median.point_estimate,
                stddev: est.std_dev.point_estimate,
            },
        );
        return Ok(());
    }
    for entry in std::fs::read_dir(dir).with_context(|| format!("reading {}", dir.display()))? {
        let path = entry?.path();
        if path.is_dir() && path.file_name().is_some_and(|n| n != "report") {
            walk(&path, out)?;
        }
    }
    Ok(())
}

fn read<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T> {
    let text = std::fs::read_to_string(path)?;
    serde_json::from_str(&text).with_context(|| format!("parsing {}", path.display()))
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_by(|a, b| a.total_cmp(b));
    let n = values.len();
    if n % 2 == 1 {
        values[n / 2]
    } else {
        (values[n / 2 - 1] + values[n / 2]) / 2.0
    }
}

/// Combines the samples of several rounds. The headline number is the median over the rounds of
/// the per-round mean; the range spans all confidence intervals, so that a change is only
/// considered real if it is larger than the spread between rounds.
pub fn aggregate(rounds: &[BTreeMap<String, Sample>]) -> Results {
    let mut names: Vec<&String> = rounds.iter().flat_map(|r| r.keys()).collect();
    names.sort();
    names.dedup();
    names
        .into_iter()
        .map(|name| {
            let samples: Vec<&Sample> = rounds.iter().filter_map(|r| r.get(name)).collect();
            let col = |f: fn(&Sample) -> f64| samples.iter().map(|s| f(s)).collect::<Vec<_>>();
            let estimate = Estimate {
                mean_ns: median(&mut col(|s| s.mean)),
                min_ns: col(|s| s.lo).into_iter().fold(f64::INFINITY, f64::min),
                max_ns: col(|s| s.hi).into_iter().fold(f64::NEG_INFINITY, f64::max),
                median_ns: median(&mut col(|s| s.median)),
                stddev_ns: median(&mut col(|s| s.stddev)),
                rounds: samples.len() as u32,
            };
            (name.clone(), estimate)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(mean: f64, lo: f64, hi: f64) -> Sample {
        Sample {
            mean,
            lo,
            hi,
            median: mean,
            stddev: 1.0,
        }
    }

    #[test]
    fn aggregates_over_rounds() {
        let rounds = vec![
            BTreeMap::from([("a".to_string(), sample(10.0, 9.0, 11.0))]),
            BTreeMap::from([("a".to_string(), sample(30.0, 29.0, 31.0))]),
            BTreeMap::from([("a".to_string(), sample(12.0, 11.0, 13.0))]),
        ];
        let agg = aggregate(&rounds);
        let a = agg["a"];
        assert_eq!(a.mean_ns, 12.0);
        assert_eq!((a.min_ns, a.max_ns, a.rounds), (9.0, 31.0, 3));
    }

    #[test]
    fn reads_criterion_layout() {
        let dir = std::env::temp_dir().join(format!("ab-test-{}", std::process::id()));
        let new = dir.join("g").join("f").join("new");
        std::fs::create_dir_all(&new).unwrap();
        std::fs::write(new.join("benchmark.json"), r#"{"full_id":"g/f"}"#).unwrap();
        let stat =
            r#"{"confidence_interval":{"lower_bound":1.0,"upper_bound":3.0},"point_estimate":2.0}"#;
        std::fs::write(
            new.join("estimates.json"),
            format!(r#"{{"mean":{stat},"median":{stat},"std_dev":{stat}}}"#),
        )
        .unwrap();
        let got = collect(&dir).unwrap();
        assert_eq!(got["g/f"].mean, 2.0);
        std::fs::remove_dir_all(dir).unwrap();
    }
}
