//! Parses the machine-readable output of gungraun (`--output-format=json`).
//!
//! Gungraun prints one JSON object per benchmark to stdout, everything else goes to stderr.
//! A benchmark has one profile per valgrind tool; callgrind gives the instruction counts and
//! DHAT, if enabled for the benchmark, the heap numbers.

use crate::model::{Metrics, Results};
use anyhow::{Context, Result};
use serde_json::Value;

fn metric(profile: &Value, name: &str) -> Option<u64> {
    let v = &profile["data"]["total"]["metrics"][name]["values"]["new"];
    v.as_u64().or_else(|| v.as_f64().map(|f| f as u64))
}

/// Parses the stdout of one gungraun benchmark target.
pub fn parse(stdout: &str) -> Result<Results> {
    let mut out = Results::new();
    for line in stdout.lines().filter(|l| l.trim_start().starts_with('{')) {
        let bench: Value = serde_json::from_str(line).context("parsing gungraun output")?;
        let (Some(module), Some(id)) = (bench["module_path"].as_str(), bench["id"].as_str()) else {
            continue;
        };
        let profiles = bench["profiles"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let tool = |name: &str| profiles.iter().find(|p| p["tool"] == name);
        let Some(callgrind) = tool("Callgrind") else {
            continue;
        };
        let dhat = tool("DHAT");
        let get = |name: &str| metric(callgrind, name);
        let (Some(instructions), Some(estimated_cycles)) = (get("Ir"), get("EstimatedCycles"))
        else {
            continue;
        };
        out.insert(
            format!("{module}::{id}"),
            Metrics {
                instructions,
                estimated_cycles,
                l1_hits: get("L1hits").unwrap_or(0),
                ll_hits: get("LLhits").unwrap_or(0),
                ram_hits: get("RamHits").unwrap_or(0),
                heap_bytes: dhat.and_then(|d| metric(d, "TotalBytes")),
                heap_blocks: dhat.and_then(|d| metric(d, "TotalBlocks")),
            },
        );
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    const LINE: &str = r#"{"module_path":"scc::scc::tarjan","id":"ring_0","profiles":[
        {"tool":"Callgrind","data":{"total":{"metrics":{"Ir":{"values":{"new":100,"old":90}},
        "EstimatedCycles":{"values":{"new":150}},"L1hits":{"values":{"new":7}},
        "LLhits":{"values":{"new":2}},"RamHits":{"values":{"new":1}}}}}},
        {"tool":"DHAT","data":{"total":{"metrics":{"TotalBytes":{"values":{"new":4096}},
        "TotalBlocks":{"values":{"new":3}}}}}}]}"#;

    #[test]
    fn reads_callgrind_and_dhat() {
        let results = parse(&LINE.replace('\n', "")).unwrap();
        let m = results["scc::scc::tarjan::ring_0"];
        assert_eq!(
            (m.instructions, m.estimated_cycles, m.l1_hits),
            (100, 150, 7)
        );
        assert_eq!((m.heap_bytes, m.heap_blocks), (Some(4096), Some(3)));
    }

    #[test]
    fn ignores_everything_that_is_not_json() {
        assert!(parse("Gungraun result: Ok.\n").unwrap().is_empty());
    }
}
