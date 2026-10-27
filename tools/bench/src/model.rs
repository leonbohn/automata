//! Data shared between the engine, the database, the reports and the dashboard.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// What valgrind reports for one benchmark. Everything is an exact count: running the same
/// code twice gives the same numbers up to tiny perturbations (kernel, address space layout).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Metrics {
    /// Executed instructions (callgrind `Ir`). The number all verdicts are based on.
    pub instructions: u64,
    pub estimated_cycles: u64,
    pub l1_hits: u64,
    pub ll_hits: u64,
    pub ram_hits: u64,
    /// Total bytes allocated on the heap (DHAT), for benchmarks that are run under DHAT.
    pub heap_bytes: Option<u64>,
    /// Total number of heap allocations (DHAT).
    pub heap_blocks: Option<u64>,
}

/// The quantity that is graphed and compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum Metric {
    #[default]
    Instructions,
    EstimatedCycles,
    HeapBytes,
    HeapBlocks,
}

impl Metric {
    pub const ALL: [Metric; 4] = [
        Metric::Instructions,
        Metric::EstimatedCycles,
        Metric::HeapBytes,
        Metric::HeapBlocks,
    ];

    pub fn key(self) -> &'static str {
        match self {
            Metric::Instructions => "instructions",
            Metric::EstimatedCycles => "estimated_cycles",
            Metric::HeapBytes => "heap_bytes",
            Metric::HeapBlocks => "heap_blocks",
        }
    }

    pub fn label(self) -> &'static str {
        match self {
            Metric::Instructions => "instructions",
            Metric::EstimatedCycles => "estimated cycles",
            Metric::HeapBytes => "heap bytes allocated",
            Metric::HeapBlocks => "heap allocations",
        }
    }

    pub fn parse(key: &str) -> Metric {
        Metric::ALL
            .into_iter()
            .find(|m| m.key() == key)
            .unwrap_or_default()
    }
}

/// Benchmark name (`file::group::function::id`, e.g. `scc::scc::tarjan::ring_0`) to metrics.
pub type Results = BTreeMap<String, Metrics>;

/// A wall-clock measurement of criterion. Only shown in the detail view of a run, never
/// compared: it depends on the machine and on what else it was doing.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct WallClock {
    pub mean_ns: f64,
    pub lo_ns: f64,
    pub hi_ns: f64,
}

pub type WallResults = BTreeMap<String, WallClock>;

/// Everything measured for one revision.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Measured {
    pub results: Results,
    pub wall: WallResults,
}

/// Describes the machine and toolchain a run happened on.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct EnvInfo {
    pub host: String,
    pub cpu: String,
    pub kernel: String,
    pub rustc: String,
    pub valgrind: String,
    pub pinned_cpu: Option<String>,
}

pub fn fmt_count(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::new();
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push('\u{202f}');
        }
        out.push(c);
    }
    out
}

/// A count with a unit suffix, such as `1.44 M` for 1 438 325.
pub fn fmt_short(n: u64) -> String {
    const UNITS: [(&str, f64); 3] = [("G", 1e9), ("M", 1e6), ("k", 1e3)];
    for (unit, scale) in UNITS {
        if n as f64 >= scale {
            return format!("{:.2} {unit}", n as f64 / scale);
        }
    }
    n.to_string()
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_counts() {
        assert_eq!(fmt_short(999), "999");
        assert_eq!(fmt_short(1_438_325), "1.44 M");
        assert_eq!(fmt_count(1_438_325), "1\u{202f}438\u{202f}325");
        assert_eq!(Metric::parse("heap_bytes"), Metric::HeapBytes);
        assert_eq!(Metric::parse("nonsense"), Metric::Instructions);
    }
}
