# Performance Notes: Porting Tricks from Spot

This document collects performance techniques found in the Spot C++ library
(source at `/sam/Rust/spot`), together with ideas for how to port or adapt them
in this crate, plus additional Rust-specific ideas that Spot cannot use.
Each entry references the relevant Spot source file so it can be consulted
directly.

A **status after issue #30** section at the end tracks which items the API
redesign already covers, and a final section collects ways to go *beyond*
Spot rather than merely matching it.

Spot's speed comes from a small number of structural decisions rather than
micro-optimizations. The most important ones, in rough order of impact:

1. Edge-centric "flat digraph" storage with intrusive successor chains.
2. Pervasive use of small unsigned integer indices instead of pointers/Rc.
3. Hash-consing / interning of formulas and BDD-based label representation.
4. Fixed-size memory pools with intrusive free lists.
5. Cheap bit-vector and bitset primitives (SSO).
6. Aggressive iterator/object recycling instead of per-iteration allocation.

---

## 1. Flat digraph storage with intrusive successor chains

**Spot source:** `spot/graph/graph.hh` (the whole file), used by
`spot/twa/twagraph.hh`.

The core data structure of Spot is a template `digraph` that stores:

- One `std::vector<edge_storage>` holding **all** edges, each edge being a
  POD of `{ dst, next_succ, src, <edge data> }` — for `twa_graph` exactly
  three `unsigned` fields plus BDD + acceptance mark.
- One `std::vector<state_storage>` where each state keeps `succ` (first
  outgoing edge) and `succ_tail` (last outgoing edge, for O(1) appending).

Outgoing edges of a state form an **intrusive singly-linked list threaded
through the edge vector** (`next_succ`, with 0 as null sentinel since edge 0
is reserved). There is no per-state adjacency vector, no `Vec<Vec<Edge>>`.

Why this is fast:

- **One allocation** for the entire graph; edges live in one contiguous
  vector (good for bulk iteration and cache behavior).
- Iterating `state_out(s)` is a tiny loop over `next_succ` with **zero
  allocation** — the iterator is just `{graph*, current_edge}` (two words).
- Appending an edge is O(1) via `succ_tail`, no sorting or scanning.
- Edge *removal* is handled lazily: deleted edges get `next_succ` pointing to
  themselves, so the global "all edges" iterator skips them in O(1)
  (`all_edge_iterator::skip_()`: `while (t < s && tv_[t].next_succ == t)`).
- `defrag_states()` compacts vectors after bulk deletions rather than paying
  for tombstones forever.

**Port to Rust:**

- The `ts::impls::linked` module already looks close to this idea. Make the
  "flat edge vector + intrusive succ chain" the *one* canonical dense
  representation, and treat every other representation as a view over it.
- Use `u32` state and edge indices (a "sentinel 0" reserved edge makes
  `Option<u32>` unnecessary — `NonZeroU32` if you want `Option` for free).
- Provide an `out_edges(state) -> impl Iterator` that is a by-value iterator
  (no borrow of the graph object beyond a slice access per step, or store
  a raw slice reference in the iterator). Rust iterators over `&self` are
  fine here because the chain walk only touches the edge vector.
- Implement edge deletion as lazy tombstoning + periodic compaction
  (`defrag`), not eager vector surgery.

## 2. Indices, not pointers; recycling, not allocating

**Spot source:** `spot/twa/twa.hh` (`iter_cache_`, `release_iter`),
`spot/twa/twagraph.hh` (`twa_graph_state::clone()` returns `this`,
`destroy()` is a no-op).

Because states are indices into the state vector, "cloning" a state is free
and reference counting does not exist on the hot path. On-the-fly algorithms
that need the abstract `twa_succ_iterator` interface recycle iterators in a
one-slot cache (`iter_cache_`) instead of allocating per visited state.

**Port to Rust:**

- Avoid `Rc<...>`/`Arc<...>` for per-state/per-edge data entirely; indices
  are cheaper and remove borrow-checker friction in algorithms.
- Where an iterator object must be created repeatedly (e.g. BFS/DFS visiting
  millions of states), offer a *reusable cursor* API:
  `struct SuccCursor<'a> { graph: &'a G, current: u32 }` with
  `fn step(&mut self)`, so a search loop allocates nothing at all.
  Spot's `state_out::recycle()` is exactly this.

## 3. Hash-consing of formulas (`fnode`)

**Spot source:** `spot/tl/formula.hh`, `spot/tl/formula.cc`.

LTL formulas are interned in a global unique table:

- An `fnode` is a single heap allocation of `sizeof(fnode) + (n-1) *
  sizeof(child)` — **children are stored inline** in a trailing array, so
  visiting children is pointer-chasing within one cache line or two.
- Structural equality is **pointer equality**; the node `id_` doubles as the
  hash value (`id_` is assigned from a global counter).
- Nodes carry a **precomputed property bitfield** (`is_`:
  syntactic-safety/recurrence/persistence/…, computed at construction) so
  later checks are a single bit test instead of a tree walk.
- Reference counts exist but are `uint16` and destructors are trivial —
  formulas are only freed via the pool.
- Boolean short-circuiting in `multop_build_and_or` merges sorted child
  vectors *at construction time*, keeping children canonically sorted, which
  makes equality checks cheap and enables the hash-consing to hit.

**Port to Rust:**

- If/when temporal-logic formulas enter this crate, use an arena
  (`typed-arena`/`bumpalo` or `Vec<Node>` with `u32` indices) plus a
  `HashMap<u64, u32>` unique table. Node equality then becomes
  `(index_a == index_b)`; hash is the id.
- Precompute syntactic-class flags on construction and expose them as
  `is_xxx()` bit tests.
- For `Expression`s over propositional alphabets, note this is exactly what
  a BDD is (see next point).

## 4. BDD-labeled edges (shared, canonical edge labels)

**Spot source:** `spot/twa/bdddict.hh`, `bdd` package (BuDDy fork under
`/sam/Rust/spot/buddy`).

Edge labels are BDDs. Consequences:

- Every label is canonical: comparing two labels is a single integer
  comparison of BDD node indices; hashing a label is hashing one integer.
- Labels with common structure share memory (a `p ∧ q` edge and an `p` edge
  share the `p` node).
- Products/compositions can compute label conjunctions (`bdd_and`) as
  near-pointer ops, and "is this label ⊥?" is `label == bddfalse`.

This crate currently uses `biodivine-lib-bdd` for
`alphabet::propositional`. That is a functional, hash-consed BDD —
correct, but noticeably slower than BuDDy-style table-based BDDs with an
operation cache.

**Port / improve:**

- Profile the BDD layer separately; if it shows up, consider
  - caching/limiting `to_string`/printing of expressions,
  - precomputing a **symbolic transition matrix** for deterministic
    automata: a `Vec<ExpressionId>` indexed by `[state][symbol]` so
    product/simulation code never re-evaluates expressions
    (see also "DFA-style dense transition function" below),
  - or porting a BuDDy-style BDD: nodes in a single `Vec<Node>`, unique
    table + computed-table per operation, `u32` node handles. This is a
    well-defined, self-contained subproject.

## 5. Fixed-size and multiple-size memory pools

**Spot source:** `spot/misc/fixpool.hh`, `spot/misc/mspool.hh`.

Spot allocates fnode children, states, and other same-sized objects from
hand-written pools:

- Bump allocation from big chunks (`(size > 128 ? size : 128) * 8192 - 64`
  bytes per chunk) with an **intrusive free list** threaded through free
  blocks (the `block_ { block_* next; }` trick: the freelist pointer is
  stored *in* the free block itself, so the pool costs zero extra memory).
- `multiple_size_pool` keeps one freelist per rounded size class.
- Sizes are rounded to powers of two / max alignment for cheap alignment and
  possible bit-trick division.
- Debug builds wire the pool into Valgrind (`VALGRIND_MALLOCLIKE_BLOCK`) so
  memory errors are still caught — worth copying the *idea* (pool can be
  audited in debug builds).

**Port to Rust:**

- Rust rarely needs this for `Vec`-backed data (the allocator already does
  size-class pooling), but it pays off for **many small fixed-size nodes**
  (formulas, BDD nodes, edge data in on-the-fly constructions). Consider a
  `bumpalo`-backed arena or a `typed_arena`-style `Vec<T>` pool where indices
  replace pointers — in Rust the vector-index approach is both safe and
  usually faster than a freelist pool.

## 6. Small-size-optimized bit vectors and bitsets

**Spot source:** `spot/misc/bitvect.hh` (also `spot/twa/acc.hh`
`mark_t` as a word-backed set of acceptance marks).

- `bitvect` stores the first block **inline** (`local_storage_`) and only
  mallocs when growing beyond one machine word — classic SSO.
- `mark_t` (acceptance sets on an edge) is a plain unsigned word when the
  automaton has ≤ 32/64 acceptance sets, so `&`, `|`, `==`, `is_subset` are
  single ALU ops. Acceptance computations (degeneralization, SCC handling)
  run on these words.

**Port to Rust:**

- Represent acceptance colors as a bitset type that is a `u64` when the
  number of colors fits, falling back to `Vec<u64>` (a small
  `enum Mark { Inline(u64), Spilled(Box<[u64]>) }` or a const-generic
  `ArrayVec`). This crate's `fixedbitset` dependency is heavier than needed
  on hot paths; check with a benchmark before replacing, but a
  `u64`-fast-path is nearly free to add.
- Same for "visited/reached" sets in traversals: use a `Vec<u64>` bitmask
  keyed by state index instead of `HashSet<Idx>` (rustc-hash or not).
  Spot's sccinfo and emptiness checks do exactly this.

## 7. Integer hashing tricks

**Spot source:** `spot/misc/hashfunc.hh`.

- `wang32_hash`, `knuth32_hash` (`(key >> 3) * 2654435761` — good for
  pointers/aligned values), FNV over sequences.
- Used everywhere state sets / seen sets are hashed.

**Port to Rust:**

- Mostly obsoleted by Rust's `FxHashMap`/`rustc-hash` (already a
  dependency — good). The actionable lesson is Spot's *discipline*: keys are
  plain integers (state ids, edge ids, BDD handles), never structs requiring
  deep hashing. Prefer `indexmap`/`FxHashMap<Idx, V>` with `Idx = u32`, and
  precompute hashes once (`id_` as hash) rather than rehashing composite
  structures on every lookup.

## 8. Miscellany worth stealing

- **`SPOT_ASSUME` / `__builtin_unreachable`** (common.hh): in Rust use
  `debug_assert!` + `unreachable_unchecked()` via a small macro in release
  builds — helps the optimizer in match dispatch over operator/state enums.
  (Only with real invariants; misuse is UB.)
- **`SPOT_UNLIKELY`** → `#[cold]` / `core::intrinsics::likely` (or the
  `likely` crate) on hot error paths.
- **On-the-fly product** (`twaproduct.hh`): states of a product are pairs of
  state indices computed lazily, with a hash map `(s1,s2) -> s`. Keep this
  pattern for `operations/product.rs`; key the map by `(u32, u32)` packed
  into a `u64` if possible.
- **Named properties attached to the automaton** (`twa::prop_*`):
  cheap boolean hints (`state-based acc`, `deterministic`, `inherently
  weak`) carried alongside the automaton let algorithms skip whole passes.
  Spot updates these through every construction. Keeping a
  `properties: PropertySet` on automata (already partially present via type
  system) pays off; consider runtime flags for properties the type system
  can't express, and *maintain them* through operations.
- **`iter_cache_`** single-slot iterator recycling (see §2).
- **`killer_edge_iterator`** (graph.hh): an out-edge iterator that unlinks
  edges from the successor chain as it iterates, enabling O(out-degree)
  edge removal without a second pass. Nice pattern for pruning algorithms
  (`purge_dead_states`, simulation pruning).
- **`defrag_states`** (twagraph.hh): after bulk deletions, compact the state
  and edge vectors using a renumbering map, with a callback hook so caches
  keyed by old ids can be fixed up. If the `shrinkable` module does eager
  deletion, consider defragmentation-on-demand instead.
- **Parallel policy** (common.hh `parallel_policy`, graph.hh
  `sort_edges_srcfirst_` parallel variant): algorithms accept a thread
  budget instead of deciding themselves. Spot parallelizes only the few
  places that pay (edge sorting, `scc_info`). In Rust, prefer `rayon` on
  embarrassingly parallel bulk passes (edge sort, SCC of disjoint
  components) and keep traversals single-threaded and allocation-free.

## 9. Additional Rust-specific ideas (not in Spot)

1. **SoA edge storage where profitable.** Spot's edge records are 16–24
   bytes. For algorithms that only need `dst` (BFS, reachability, product),
   a split layout `Vec<u32 dst>` + `Vec<Label>` halves the memory traffic of
   those passes. A `CSR` (compressed sparse row) snapshot view — sort edges
   by source, store offsets — makes sequential out-edge iteration *perfectly*
   cache-friendly for read-heavy passes (minimization, quotient, SCC).
   Cheap to build in O(n) from the flat representation; consider offering
   both views ("mutable intrusive" for construction, "CSR" for analysis).

2. **Dense transition function for deterministic automata.** For a DFA
   over a finite alphabet, the fastest membership test is
   `trans[(state as usize) * k + symbol as usize]` with `k` precomputed and
   symbols mapped to `0..k` at parse time. This is what makes DFA
   operations in practice instant; keep it as a specialized representation
   behind the `Deterministic` trait (`Vec<u32>`, sentinel `u32::MAX` for
   missing edges) used by `run`/`path`/`omega` acceptance checks.

3. **Copy-on-write only at the boundaries.** Cheap `clone()` of automata via
   `im`/persistent vectors is tempting but slow; instead make automata
   cheaply *sharable* (`&G`) and let algorithms take snapshots where needed.

4. **Branchless acceptance checking.** Parity/Rabin acceptance evaluation on
   runs is a hot inner loop; evaluate priority vectors with `min`/`max`
   reductions (`itertools::min`, `u32::min`) instead of match chains. For
   deterministic parity, precompute per-state priority into a `Vec<u8>`.

5. **Iteration order discipline.** Rust `HashMap` iteration is random —
   good for tests but bad for reproducible benchmark comparisons. Spot's
   determinism makes profiling and regression-tracking sane. Where iteration
   order leaks into output, use `indexmap`/sorted vectors or BTree where it
   matters (already available as dependencies).

6. **`#[inline]` audit + PGO-friendly crates.** Keep the edge iterator
   `.step()`, `mark_t` bit ops, and expression-id comparison inline (they
   are trivially small). Measure with `cargo flamegraph`/`criterion`
   (already set up) and consider `-C target-cpu=native` guidance in docs for
   benching.

7. **Avoid `tracing` on the hot path.** Spot uses no logging in inner loops;
   either gate per-edge `tracing` calls behind a feature or make sure the
   subscriber-disabled path is a cheap check (it usually is, but a
   `Span::enter` per edge is not).

---

## Status after the #30 API redesign

Issue #30 (and its sub-issues) covers a large part of the original list
above. Mapping the `Suggested order of attack` against the roadmap:

| #30 item | PERFORMANCE.md items it covers | Verdict |
|---|---|---|
| #41 ids, `CompactIdMap`, `StateSet`/`StateMap`, one bitset crate | §2 (u32 indices, indices-not-pointers), §6 (word-backed visit sets — replaces `BTreeSet`/SipHash visited sets, P8), §7 (integer hashing discipline) | **Covered** |
| #42 `Cow` colours | Part of §2 (owned `state_color()`/`color()` clones per query) | **Covered** |
| #43 traversal module `Bfs`/`Dfs`/`AccessWords` | §2 (allocation-free cursors), the P9 minimal-representatives restart problem | **Covered** |
| #46 `Automaton<T, Z>` + `Semantics<T, W>` | Removes `OMEGA`/`DET` const generics (type-level, not per-se) | **Covered** (enabler) |
| #47 allocation-free omega runs | §2 cursors on the run path, P12 (`spoke_vec`/`cycle_vec`/`Word::nth` per step) | **Covered** |
| #48 one `EdgeRef`, merged adapters, product fast path | P5/P11 (linear `contains_state`, O(d_l·d_r) product matching), lazy adapter re-evaluation | **Covered** |
| #49 `Linked` storage with stable `EdgeId`s and compact layout | Parts of §1 (O(1) `remove_edge(id)` replaces lazy tombstoning as the *mechanism*; edge shrinks from ~80 to ~40 bytes of bookkeeping if in-links move out — decision 4 keeps them in for now) | **Partially covered** — see *remaining* below |
| #50 `Dense` storage (n × |A| table over `IndexedAlphabet`) | §9.2 dense transition function | **Covered** |
| #54 `IntoTransitions`/`FromTransitions` | P4 (multi-pass collect, 6–11× gap vs `clone`) | **Covered** |
| #55 `Sccs` problem type | P8 (three ad-hoc densify paths), shared SCC entry point | **Covered** |
| #56/#57 equivalence/witnesses, `Minimize`, fast `Quotient` | P10, P14 | **Covered** |

### What remains after #30

1. **Flat digraph with intrusive successor chains (§1).** The redesigned
   `Linked` still stores per-state edge lists; Spot's single contiguous
   `Vec<edge_storage>` with `next_succ` threading and lazy tombstoning +
   `defrag_states` compaction is *not* part of #30. `EdgeId` gives O(1)
   removal, but the memory-locality win of one flat vector is still open.
2. **`Csr` frozen snapshot view (§9.1).** The redesign explicitly defers it
   (`// later: pub struct Csr`). After phase 3 this is the natural next
   storage: an O(E) snapshot from `Linked`/`Dense` for read-heavy passes
   (minimization, quotient, SCC, inclusion).
3. **BDD layer (§4).** Unchanged by #30 — `biodivine-lib-bdd` stays for
   `Linked`/propositional automata. If profiling after 0.2 shows it hot, a
   BuDDy-style table BDD (nodes in one `Vec`, unique table + computed table
   per operation, `u32` handles) is a self-contained follow-up project.
4. **SoA edge splitting (§9.1).** Not in #30. Once `Csr` exists, a variant
   that splits `dst` from label/colour arrays halves memory traffic for
   structure-only passes.
5. **Branchless priority evaluation (§9.4).** #47 fixes the run *allocation*
   problem, not the acceptance-evaluation inner loop. Keep this for after the
   omega-run rewrite lands.
6. **Micro items (§8, §9.6, §9.7).** `#[inline]` audits, `unreachable_unchecked`
   hints, `#[cold]` error paths, `tracing` off the hot path (P16 flags one
   `tracing::info!` in iterative Tarjan — check whether #55 removes it).
7. **Word-backed acceptance marks specifically (§6).** #41 standardizes
   *state* sets; a `mark_t`-style `u64`-fast-path enum for acceptance colours
   (falling back to `fixedbitset`) should ride along with #52 (`WriteHoa`,
   acceptance on the new `Automaton`) so all acceptance computations benefit.
8. **Parallelism (§8).** Not in #30. Once storages are stable, `rayon` on
   bulk passes (edge sort, per-SCC work) is cheap to add.

---

## Going beyond Spot: what they do not do

Can we beat Spot? In the domains where this crate operates (explicit,
finite-alphabet automata — DFAs/DPAs over `CharAlphabet`-style alphabets),
yes, plausibly, for structural reasons Spot cannot fix without breaking
its C++ API. Where Spot wins is BDD-heavy, propositional-label work
(large LTL → TGBA translations); that is a different arena (see §4).

Spot's own ceiling comes from four invariants of its design:

1. **One representation for everything.** Every `twa_graph` stores a BDD
   label per edge, even when the alphabet is two symbols and labels are
   single `p` or `¬p`. There is no dense `n × |A|` storage; `#50`'s `Dense`
   has no Spot equivalent. For explicit automata this is an entire
   representation Spot never specializes to.
2. **Virtual dispatch on the fly.** Spot's on-the-fly interface
   (`twa_succ_iterator` with virtual `first()`/`next()`/`dst()`, heap-
   allocated and recycled through `iter_cache_`) exists so that any
   algorithm can consume any representation. Every successor step is a
   virtual call through a pointer-chased iterator. In Rust, monomorphized
   generic code over `EdgesFrom<'a>` iterators compiles to the same tight
   loop as hand-written code, with no dynamic dispatch and no allocation.
   This is the structural gap we can exploit: an iterator *type* instead
   of an iterator *object*.
3. **No SIMD.** Verified: no `__m*` intrinsics anywhere in `spot/` (only a
   robin-hood hash header). Spot's bitvectors, acceptance marks and
   simulation signatures are scalar. Partition refinement
   (minimization) and signature hashing over bitsets is exactly the kind
   of code that autovectorizes or takes explicit `std::simd` in Rust.
4. **Sequential core.** Spot has `parallel_policy`, but it parallelizes
   only edge sorting and a few `scc_info` uses; `twacube` exists for
   concurrent model checking but is a separate representation. A Rust
   crate with `Send + Sync` storages and `rayon` can parallelize the same
   bulk passes by default with far less machinery.

Concrete opportunities, in order of expected payoff:

- **`Dense` + const-generic specialization (#50 + follow-ups).** Compile
  a DFA transition table into `Vec<u32>` (or even `[u8; k]` per state for
  small alphabets and ≤ 256 states) with symbols pre-mapped to indices at
  parse time. A membership query becomes one indexed load; Spot must
  compare BDD labels for the same question. This alone should make DFA
  runs, products and subset construction over explicit alphabets faster
  than Spot's equivalents.
- **Monomorphized algorithms.** Keep #30's `EdgesFrom<'a>: Iterator`
  (by-value, not dyn) as *the* algorithm interface and resist adding a
  `dyn TransitionSystem` fast path that reintroduces virtual dispatch.
  Combined with `#[inline]` on `step()`/`color()` accessors, whole
  traversals can stay in registers/L1 in a way Spot's vtable-based
  iterators cannot.
- **`Csr` + SoA snapshots.** Freeze into `Vec<u32 dst>` + offset array;
  structure-only passes (SCC, reachability, minimization sweeps) then
  stream contiguous memory, optionally via `rayon` chunks per offset
  range. Spot has no read-optimized snapshot at all — it re-walks the
  intrusive chains every time.
- **SIMD/bitset partition refinement.** In `Minimize`/`Quotient`, encode
  each block's per-symbol target signature as bitset rows and hash
  blocks with `u64::xored`-style reductions (`wide`/`std::simd` or plain
  chunks of `u64`, which LLVM vectorizes). Spot's `simulation.cc` works
  on BDD-label equivalence classes instead.
- **A modern allocator and no exceptions on the hot path.** `mimalloc`
  (feature-gated) typically beats glibc malloc for the allocation
  pattern of bulk construction; Spot uses system `malloc` throughout.
  Also, Rust guarantees no unwinding through our inner loops, which
  removes the cleanup scaffolding C++ generates around throwing code.
- **Thread-local / concurrent BDD tables.** If the BuDDy-style BDD from
  §4 ever materializes: BuDDy is a global singleton with a unique table
  guarded essentially by convention; a Rust BDD with per-thread computed
  tables and a shared unique table (`arc-swap`d or sharded) would
  parallelize BDD operations that Spot must serialize. This is the
  arena where Spot is strongest, so treat it as ambitious.
- **PGO/LTO and `target-cpu` guidance** for benchmarking parity: Spot
  ships generic `-O2` builds. Not a code change, but part of any honest
  comparison.

Honest caveats: Spot's *algorithmic* portfolio (degeneralization,
simulation, SAT-based minimization, `translate` pipeline) is far larger
than anything planned here, so "faster" claims must be scoped to the
constructions both libraries implement — the redesign's `Linked`/`Dense`
   world versus `twa_graph` on explicit inputs, and, eventually, the
   BDD front.
