//! The benchmarks read the HOA files in `benches/fixtures`. A fixture that cannot be read would
//! only show up when a benchmark is run under valgrind, so check them all here.

#![cfg(feature = "hoa")]

use automata::{TransitionSystem, hoa::HoaString};
use std::path::{Path, PathBuf};

fn fixtures(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("fixture directory") {
        let path = entry.expect("directory entry").path();
        if path.is_dir() {
            fixtures(&path, out);
        } else if path.extension().is_some_and(|e| e == "hoa") {
            out.push(path);
        }
    }
}

#[test]
fn all_fixtures_are_deterministic_parity_automata() {
    let mut files = Vec::new();
    fixtures(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("benches/fixtures"),
        &mut files,
    );
    assert!(files.len() > 50, "only {} fixtures found", files.len());
    for file in files {
        let text = std::fs::read_to_string(&file).expect("readable fixture");
        let automaton = HoaString::from(text)
            .pop::<true>()
            .unwrap_or_else(|| panic!("{} cannot be parsed", file.display()))
            .into_dpa()
            .unwrap_or_else(|e| panic!("{} is not a parity automaton: {e}", file.display()));
        assert!(automaton.size() > 0, "{} is empty", file.display());
    }
}
