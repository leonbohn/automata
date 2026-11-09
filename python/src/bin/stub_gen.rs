//! Generates `py/automata/_automata/__init__.pyi`; run with `cargo run --bin stub_gen`.
fn main() -> pyo3_stub_gen::Result<()> {
    _automata::stub_info()?.generate()?;
    // pyo3-stub-gen qualifies the base of our exceptions as `builtins.X`; they live in this module.
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/py/automata/_automata/__init__.pyi"
    );
    let stub = std::fs::read_to_string(path)?;
    std::fs::write(
        path,
        stub.replace("(builtins.AutomataError)", "(AutomataError)"),
    )?;
    Ok(())
}
