//! Reading and writing automata in the HOA format.
//!
//! Run with `cargo run --example hoa` to use a built-in automaton, or pass the path of a file
//! that contains deterministic parity or Büchi automata: `cargo run --example hoa -- file.hoa`.

use automata::States;
use automata::hoa::{HoaString, WriteHoa};

const EXAMPLE: &str = r#"HOA: v1
States: 2
Start: 0
acc-name: parity min even 3
Acceptance: 3 Inf(0) | (Fin(1) & Inf(2))
AP: 2 "a" "b"
--BODY--
State: 0
[0 & !1] 1 {1}
[!0 & 1] 0 {0}
State: 1
[0 & !1] 0 {1}
[!0 & 1] 1 {2}
--END--
"#;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let text = match std::env::args().nth(1) {
        Some(path) => std::fs::read_to_string(path)?,
        None => EXAMPLE.to_string(),
    };

    // a string can contain several automata, `pop` returns them one after the other
    let mut hoa = HoaString::from(text);
    while let Some(automaton) = hoa.pop::<true>() {
        println!("read an automaton with {} states", automaton.state_count());

        // the automaton has a generic acceptance condition, make it a parity automaton
        let dpa = automaton.into_dpa()?;
        println!("{}", dpa.to_hoa());
    }
    Ok(())
}
