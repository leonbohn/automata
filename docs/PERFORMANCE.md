# Performance opportunities

A ranked list (most impactful first) of places where the crate could be made faster, found by
reviewing the transition system storages (`LinkedTs`, `DenseTs`, `CsrTs`), the lazy adapters and the
algorithms built on them. Every entry names the location, the current behavior, the idea, and a
rough estimate of impact and effort. The existing `gungraun` benchmarks (`benches/ts.rs`,
`benches/dfa.rs`, `benches/scc.rs`, `benches/runs.rs`) cover most of these paths and can measure
every change.

---

## 1. O(1) symbol lookup for `Det<LinkedTs>` / `LinkedTs`

**Location:** `src/ts/impls/linked.rs` — `out_edge_position`, `Deterministic::edge`/`successor`.

**Current behavior:** `successor(q, sym)` linearly scans the out-list of `q`, matching each edge's
expression against the symbol. The doc comment on `Deterministic for Det<LinkedTs>` already admits
"there is no constant-time lookup yet". This is *the* hot path of the whole crate: every run, every
product, every exploration, every `DeterministicEdgesFrom` step goes through it. The
`successor_index_all_pairs` benchmark does `n * k` such scans, each chasing linked-list nodes that
are scattered through the `edges` vector in insertion order (cache-unfriendly, see #3).

**Idea:** for `IndexedAlphabet` alphabets keep a per-state `symbol index -> EdgeId` table (a flat
`Vec<u32>` of size `n * k`, exactly like `DenseTs::targets`, maintained on edge insert/remove, or
built lazily on first lookup and invalidated on mutation, like `DenseTs::incoming`). Lookups become
one index computation and one load instead of an O(out-degree) pointer-chasing scan.

**Impact/effort:** very high / medium. `LinkedTs` is the default storage (`DTS = Det<LinkedTs>`), so
this speeds up essentially everything; the alternative is migrating hot code to `DenseTs`/`CsrTs`,
which don't support all alphabets or in-place growth the same way.

## 2. `SubsetConstruction` recomputes everything on every edge query

**Location:** `src/ts/operations/subset.rs` — `Deterministic for SubsetConstruction::edge`.

**Current behavior:** each `edge(set, sym)` call

- re-walks the out-edges of every state in the subset,
- collects all matching edge colors into a `Vec` (cloning each) and all targets into a `StateSet`,
- sorts and dedups the targets (`normalize`) — even though a bitset-sized membership pass would do,
- linearly scans `self.expressions` to find the expression for the symbol (should be indexed,
  e.g. via `expression_map` order or `IndexedAlphabet::expression_to_index`),
- **memoizes nothing about transitions**: only the set -> id map is remembered. `edges_from` is
  `DeterministicEdgesFrom`, which calls `edge` once per alphabet symbol, so asking for the
  successors of one subset costs `k` full recomputations.

**Idea:** memoize the successor computation per `(subset id, symbol)` (the struct already uses
`RefCell` interior mutability for `states`/`ids`), index the expressions by symbol index, and use a
reusable scratch `FixedBitSet` for target collection instead of sort+dedup. Also skip the color
`Vec` when the caller only needs the target (e.g. `successor`).

**Impact/effort:** very high for NTS -> DTS determinization / medium. Subset construction is
quadratic-ish as written; with memoization each transition is computed exactly once.

## 3. Cache-unfriendly edge layout in `LinkedTs`

**Location:** `src/ts/impls/linked.rs`, `linked/linked_edge.rs` — edge vector + doubly linked lists.

**Current behavior:** edges live in a `Vec` in insertion order and each state's out-/in-edges are
chased through `out_next`/`in_next` links, i.e. a pointer chase over essentially random memory for
every `edges_from`/`predecessors` iteration. Every traversal (BFS, DFS, Tarjan, runs, products)
pays this. Additionally each edge carries 24 bytes of bookkeeping (6 `u32` links/endpoints) plus
expression and color.

**Idea:** two complementary things.

- Let `compact()` renumber edges so that the out-list of each state becomes contiguous in the edge
  vector (order states by index, then their out-edges). Iterating `edges_from` then walks
  consecutive memory; `Tarjan`/`Bfs` get noticeably faster on large systems. The `Compaction`
  mapping already exists to fix up ids.
- Consider singly linked lists plus O(d) unlink (walk to find predecessor) or tombstone-with-lazy-
  unlink to shrink the 24-byte overhead — a deliberate trade of removal cost for iteration speed;
  measure against the removal-heavy benchmarks before doing this.

**Impact/effort:** high / medium (the reordering part is contained in `compact`).

## 4. Recursive Tarjan does redundant work and a quadratic stack scan

**Location:** `src/ts/connected_components/tarjan.rs` — `Tarjan::visit`, exposed as
`tarjan_scc_recursive` / `States::sccs_recursive`.

**Current behavior:**

- The relax step is nested inside `for _a in edge.expression().symbols()` — the identical update is
  repeated once per symbol the expression matches. For `PropExpression`s matching many symbols this
  is pure duplication (and `symbols()` on BDDs is not free).
- When a root is found, the SCC boundary is located with `stack.iter().rposition(...)` — an
  O(stack) scan per SCC root, i.e. O(n^2) on long chains (the `path`/`back_edges` bench shapes).
- It recurses (stack overflow risk on deep graphs) and uses the hash-based `StateMap` when the
  bound is unknown.

**Idea:** drop the symbols loop; replace the `rposition` scan by tracking the stack segment
explicitly (as the iterative variant does with `stack.pop` until the root); or simply delete the
recursive variant and keep `tarjan_scc_iterative` (already the default for `States::sccs`).

**Impact/effort:** high where `sccs_recursive` is used / low.

## 5. `Det<LinkedTs>::add_edge` churns tombstones on replacement

**Location:** `src/ts/impls/linked.rs` — `Sproutable for Det<LinkedTs>::add_edge`.

**Current behavior:** adding an edge that overlaps an existing one first scans the out-list
(`out_edge_position`), then `remove_edge` (tombstone + relink both lists) and `insert_edge`
(relink both lists again). Builders that overwrite edges (learning algorithms, completion, tests
that re-add) accumulate 24-byte tombstones and invalid ids, and the edge ids churn so external
tables keyed by `EdgeId` must be rebuilt.

**Idea:** when exactly one edge overlaps (the common deterministic case: same expression, or a
single-symbol alphabet), overwrite its expression/color/target in place — no tombstone, stable id,
no relinking. Only fall back to remove+insert when several edges overlap.

**Impact/effort:** high for build/mutation-heavy workloads (`add_edges_*`, `builder_with_edges`
benches) / low.

## 6. `Quotient::edge` allocates and clones per query

**Location:** `src/ts/operations/quotient.rs` — `Deterministic for Quotient::edge` (~line 203).

**Current behavior:** every edge lookup iterates the whole class, queries the underlying system per
member, hashes each target through `class_of` (an `FxIndexMap`), and collects into a `BTreeSet`
plus a `Vec` of cloned colors — all to return one edge. Minimization builds a quotient and then
collects it (`mealy_partition_refinement`), so this runs `n * k` times with several allocations per
call.

**Idea:** for deterministic systems a quotient edge only needs *one* class representative's edge
(the others are equal by construction of the partition, as the commented-out `all_equal` asserts
suggest): query the first member, map its target through `class_of`, done. Also replace
`class_of: FxIndexMap<Idx, usize>` by a dense `Vec` when the state indices are dense (a
`StateMap`-style choice at construction).

**Impact/effort:** high for minimization (`minimize*` benches) / low–medium.

## 7. `is_deterministic` is O(n * d^2)

**Location:** `src/ts.rs` — `States::is_deterministic` (line ~530).

**Current behavior:** per state, all pairs of out-edges are checked with `Alphabet::overlapping`,
after collecting the edges into a `Vec`. This runs every time a `Det` storage is built from a
linked system (`Det::try_new`, `Storage::try_from_linked`, `try_into_deterministic`) and on every
`is_deterministic` call.

**Idea:** sort the state's edges by expression (or by symbol interval) and only compare adjacent
overlapping candidates — O(d log d) per state. For single-symbol expressions (`CharAlphabet`,
`Fixed`) a `FixedBitSet` of seen symbol indices gives O(d) per state.

**Impact/effort:** medium (one-off per conversion, but conversions are common) / low.

## 8. `MatchingProduct::edges_from` is a nested O(d_l * d_r) loop with expression equality

**Location:** `src/ts/operations/product.rs` — `ProductEdges::next`.

**Current behavior:** for each left edge the right edge iterator is restarted and expressions are
compared with `==`. Exploration of a product (emptiness checks, `reachable_part`, the boolean-op
benches `with_minimized`/`with_empty`/`deep_difference`) iterates `edges_from`, so each product
state costs `d_l * d_r` comparisons plus color clones for every yielded edge.

**Idea:** for deterministic sides over an `IndexedAlphabet`, merge the two (symbol-ordered) edge
lists by symbol index instead of the nested loop — O(d_l + d_r) per state. The
`Deterministic for MatchingProduct::edge` fast path already exists for single-symbol queries; the
iterator needs the same idea. Also avoid cloning both colors when the caller only reads targets.

**Impact/effort:** medium–high (automata boolean operations) / medium.

## 9. Omega-run cycle detection uses a hash map and keeps every pass

**Location:** `src/ts/run.rs` — `RunKind for Omega::run`.

**Current behavior:** `let mut seen = crate::ts::StateMap::new(None);` ignores `ts.state_bound()`,
so cycle detection always hashes (`StateMap::Sparse`) even for dense `u32` indices. Also one
observer per cycle pass is kept in a `Vec` and all of them from the first repeat onward are merged
at the end.

**Idea:** pass `ts.state_bound()` to `StateMap::new` so dense systems get a `Vec<Option<usize>>`.
(Merging must keep the passes of the loop, so the `Vec` stays, but it is bounded by the number of
distinct cycle-entry states.)

**Impact/effort:** medium (every omega acceptance check) / trivial.

## 10. Removal helpers on `LinkedTs` allocate and sort unnecessarily

**Location:** `src/ts/impls/linked.rs` — `linked_remove_state`, `filter_remove_edges`,
`out_edge_ids`/`in_edge_ids`.

**Current behavior:** `linked_remove_state` collects out ids and in ids into two `Vec`s,
concatenates, `sort_unstable`, `dedup`, then removes one by one. `filter_remove_edges` likewise
collects all matching ids into a `Vec` first. But `remove_edge` already unlinks from both lists in
O(1) and returns `None` for tombstones, so neither the sort/dedup nor the intermediate vectors are
needed: walk the out-list then the in-list, capturing `next` before unlinking.

**Idea:** in-place list-walking removal (as the `list_walking_removal_agrees_with_full_scan` test
already validates for `remove_edges_*`). No allocation, no sort, better locality.

**Impact/effort:** medium (shrink-heavy code, e.g. `remove_state` in a loop) / low.

## 11. `DenseTs` removals build the full reverse CSR

**Location:** `src/ts/impls/dense.rs` — `remove_state`, `remove_edges_to`, `slots_into`.

**Current behavior:** the first removal (or `predecessors` call) builds the reverse CSR over all
`n * k` slots and keeps it; `slots_into` additionally collects the slots into a `Vec` per call.
Removing one state from a large dense system that never queries predecessors pays O(n * k) plus an
allocation, and interleaving `add_edge` (which drops the table) with removals rebuilds it
repeatedly.

**Idea:** when the CSR is not built, find incoming edges of `q` by scanning the slot column
directly (`targets[s * k + a] == q`) without building the table, or scan `targets` once and filter;
build the CSR only when `predecessors` is actually iterated. Reuse a scratch `Vec` for `slots_into`.

**Impact/effort:** medium (mutation-heavy `DenseTs` use) / low.

## 12. Hopcroft refinement: sort per splitter and tree-based partitions

**Location:** `src/minimization/partition_refinement.rs` — `refine`, `collect_partition`;
`src/partition.rs` — `Partition<I> = Vec<BTreeSet<I>>`.

**Current behavior:** in `refine`, `found.sort_unstable()` runs on every splitter pop whenever
there is more than one edge label (Mealy case); a counting/bucket pass over the small label set
would avoid the comparison sort. `collect_partition` builds an `FxIndexMap<usize, BTreeSet<I>>`
and then sorts `BTreeSet`s; `Partition` itself stores one `BTreeSet` per class — a tree allocation
per class and pointer-chasing iteration, where sorted `Vec`s would be faster and smaller (the
classes are already built from dense indices in the minimization pipeline).

**Idea:** bucket `found` by label with a reusable `Vec<Vec<..>>` indexed by label; build partitions
as `Vec<Vec<I>>` (sorted once) or at least collect classes directly from the dense `block_of`
array with a counting pass.

**Impact/effort:** medium (the `minimize*` benches) / medium.

## 13. `LinkedTs` equality builds two hash sets per state

**Location:** `src/ts/impls/linked.rs` — `PartialEq for LinkedTs`, `edge_set`.

**Current behavior:** comparing two systems allocates an `FxIndexSet` per state per side (2n hash
sets, each hashing every edge) — e.g. in learning/equivalence loops and tests.

**Idea:** compare out-lists by sorting into two reusable scratch `Vec`s (or, since both sides are
linked lists over the same index space, intersect by walking). Reuse the scratch buffers across
states.

**Impact/effort:** low–medium / low.

## 14. `DenseTs`/`CsrTs` color storage wastes a word per slot and edges iteration scans all `k` slots

**Location:** `src/ts/impls/dense.rs`, `src/ts/impls/csr.rs` — `colors: Vec<Option<C>>`,
`DenseEdgesFrom`/`CsrEdgesFrom`.

**Current behavior:** `Option<C>` stores a discriminant per slot even though `targets[slot] != NONE`
already encodes presence (e.g. `DenseTs<char, u32>` spends 8 bytes per slot on the color array where
4 would do). `edges_from` iterates all `k` slots of a state skipping `NONE`, which is O(k) even for
near-empty rows (fine for small alphabets, wasteful for large `k`).

**Idea:** store `colors: Vec<C>` (or `MaybeUninit<C>` behind the target sentinel — requires
`unsafe`, weigh it) and, for large alphabets, a per-state list of occupied symbol indices. Also the
iterators carry redundant `slot`/`symbol_index` counters next to two slice iterators; zipping one
enumerated slice pair would generate tighter code.

**Impact/effort:** low (memory footprint, large-alphabet iteration) / low–medium.

## 15. Default `States::is_complete` builds B-tree sets per state

**Location:** `src/ts.rs` — `States::is_complete` (line ~554).

**Current behavior:** collects the universe into a `BTreeSet` once and then a `BTreeSet` of symbols
per state (via `transitions_from`, which also expands expressions into symbols). `DenseTs`/`CsrTs`
override it; `LinkedTs` (the default storage) does not, so `complete_with_colors` on linked systems
pays for it.

**Idea:** for `IndexedAlphabet` use a `FixedBitSet` of size `k` per state (the `Sproutable`
completion already does exactly this) or count distinct covered symbol indices.

**Impact/effort:** low / trivial.

## 16. Smaller items

- `src/ts/transitions_from.rs` — `TransitionsFrom::next` clones the edge color twice per first
  symbol of an edge (`self.color = Some(color.clone())` then `color.clone()` into the tuple); one
  clone suffices.
- `src/ts/impls/csr.rs` — `ReverseCsr::build` clones the offsets vector (`fill = offsets.clone()`);
  the offsets can be used as fill cursors and restored by shifting afterwards (standard CSR trick).
- `src/ts/visit.rs` — `AccessWords::expand` allocates and sorts a `Vec<(sym, target)>` per
  dequeued state; a reusable buffer or sorting only the newly discovered edges would cut
  allocations in `minimal_representatives` loops.
- `src/ts/operations/restricted.rs` — `EdgeColorRestricted::edges_from` clones `min`/`max` colors
  into every iterator; keeping references would avoid two clones per call.
- `src/ts/run.rs` — observers like `EdgeColorSet`/`EdgeColorSequence` clone the edge color per
  transition; inherent to the observer design, but `EdgeColorSet` could insert a borrowed-then-
  cloned-on-miss entry to avoid hashing twice (`contains` then `insert`).
- `src/ts/impls/linked.rs` — `compact()` allocates four new vectors; with tombstone-heavy systems
  this is fine, but the `state_map`/`edge_map` could be reused scratch space if `compact` is called
  repeatedly (e.g. via `linked_map_*`, which always compacts first).

---

## Suggested order of attack

1. #1 (lookup index) and #5 (in-place replace) — they define the speed of the default storage.
2. #2 (subset memoization) and #6 (quotient edge) — the two worst offenders in automaton-level
   algorithms.
3. #3 (edge reordering in `compact`) and #4 (Tarjan) — traversals.
4. #8–#12 as benchmark-driven follow-ups; #13–#16 are cleanups with measurable but small wins.

Every change should be validated with `./scripts/check` plus the instruction-count benchmarks
(`tools/bench`), and benchmark names must stay stable so history remains comparable.
