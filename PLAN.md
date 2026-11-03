# PLAN: automata

Goal: a published, documented, well-tested general-purpose crate for finite- and omega-word automata (DFA, NFA, Moore/Mealy, Buchi, parity, Rabin, Muller, ...) with HOA interoperability.

# The Future, so 0.3

- [ ] Boolean operations for every acceptance type where closure exists; complement for deterministic parity, Rabin, Muller.
- [ ] Emptiness and witness extraction (accepting word / lasso).
- [ ] Equivalence and inclusion checks with counterexamples.
- [ ] Minimization: Hopcroft DFA, Moore/Mealy, DPA priority reduction.
- [ ] Acceptance conversions (Buchi/Rabin/Muller to parity) and Safra determinization.
- [ ] Regex to NFA, `from_words` builders.
- [ ] Differential tests against Spot via HOA.
- [x] Learning algorithms (passive: sprout, DPAInf; active: L\*) moved from `automata-learning` into `automata::learning` (feature `learning`, #118). Open: switch `frieda` to depend on this crate, deprecate the old crate, resolve #119.
- [ ] mdBook guide in `docs/`, deployed via GitHub Pages; `CONTRIBUTING.md`; `CHANGELOG.md` is kept up to date under "Unreleased" (add an entry with every user-visible change).

## Known issues parked for later

Performance (measure with benchmarks first, see Phase 4):
- `src/ts/connected_components/tarjan.rs`: for every back edge the stack is walked linearly (`skip_while`), which can make SCC computation quadratic; the `tee()` has an unused half.
- `src/minimization/partition_refinement.rs`: open question whether edge colors can be dropped entirely when collecting into a Moore machine.

Correctness and design:
- `From<FDFA> for FWPM` (`src/families/convert.rs`) does not check that the FDFA is saturated (documented as a precondition). The check is costly; add it later, probably as an opt-in `TryFrom`.
- `PeriodicOmegaWord` should wrap a non-empty word type instead of documenting the invariant.
- `out_edge_position` / `in_edge_position` in `linked.rs` have a "make this a match" cleanup pending.
