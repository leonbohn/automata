//! Reads the result files criterion leaves in `target/criterion` (the wall-clock target).

use crate::model::{WallClock, WallResults};
use anyhow::{Context, Result};
use serde::Deserialize;
use std::path::Path;

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
}

/// Collects every benchmark below `dir` (a `target/criterion` directory) that has a `new` run.
pub fn collect(dir: &Path) -> Result<WallResults> {
    let mut out = WallResults::new();
    if dir.is_dir() {
        walk(dir, &mut out)?;
    }
    Ok(out)
}

fn walk(dir: &Path, out: &mut WallResults) -> Result<()> {
    let new = dir.join("new");
    if new.join("benchmark.json").is_file() && new.join("estimates.json").is_file() {
        let id: BenchmarkJson = read(&new.join("benchmark.json"))?;
        let est: EstimatesJson = read(&new.join("estimates.json"))?;
        out.insert(
            id.full_id,
            WallClock {
                mean_ns: est.mean.point_estimate,
                lo_ns: est.mean.confidence_interval.lower_bound,
                hi_ns: est.mean.confidence_interval.upper_bound,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_criterion_layout() {
        let dir = std::env::temp_dir().join(format!("ab-test-{}", std::process::id()));
        let new = dir.join("g").join("f").join("new");
        std::fs::create_dir_all(&new).unwrap();
        std::fs::write(new.join("benchmark.json"), r#"{"full_id":"g/f"}"#).unwrap();
        let stat =
            r#"{"confidence_interval":{"lower_bound":1.0,"upper_bound":3.0},"point_estimate":2.0}"#;
        std::fs::write(new.join("estimates.json"), format!(r#"{{"mean":{stat}}}"#)).unwrap();
        let got = collect(&dir).unwrap();
        assert_eq!(got["g/f"].mean_ns, 2.0);
        std::fs::remove_dir_all(dir).unwrap();
    }
}
