//! Data shared between the engine, the database, the reports and the dashboard.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Aggregated measurement of one benchmark over all rounds of a run. All times are nanoseconds.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Estimate {
    /// Median over the rounds of the mean estimate of each round.
    pub mean_ns: f64,
    /// Lowest lower confidence bound over all rounds.
    pub min_ns: f64,
    /// Highest upper confidence bound over all rounds.
    pub max_ns: f64,
    pub median_ns: f64,
    pub stddev_ns: f64,
    pub rounds: u32,
}

/// Benchmark name (criterion's `full_id`, e.g. `baseline/collect/clone/100000`) to estimate.
pub type Results = BTreeMap<String, Estimate>;

/// Describes the machine and toolchain a run happened on.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct EnvInfo {
    pub host: String,
    pub cpu: String,
    pub kernel: String,
    pub rustc: String,
    pub pinned_cpu: Option<String>,
    pub criterion_args: Vec<String>,
}

pub fn fmt_ns(ns: f64) -> String {
    const UNITS: [(&str, f64); 3] = [("s", 1e9), ("ms", 1e6), ("µs", 1e3)];
    for (unit, scale) in UNITS {
        if ns >= scale {
            return format!("{:.2} {unit}", ns / scale);
        }
    }
    format!("{ns:.0} ns")
}

pub fn now() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}
