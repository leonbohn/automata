//! Stateful model-based testing of storages: a sequence of random operations is applied to a
//! storage and to the naive [`Model`]; after every step both are compared.
//!
//! Operations refer to states and edges by *selectors* instead of concrete ids. A selector is
//! resolved against what currently exists in the model, so that almost every generated operation
//! is meaningful and shrinking an operation sequence keeps it valid. For operations that accept
//! unknown ids, the selector one past the last live item resolves to something that does not
//! exist, which exercises the `None` paths of the storage.

use std::collections::HashMap;

use crate::{
    TransitionSystem,
    alphabet::CharAlphabet,
    minimization::partition_refinement::{
        mealy_greatest_bisimulation, moore_greatest_bisimulation,
    },
    ts::{
        Deterministic, EdgeId, EdgeTuple, IdType, Pointed, PredecessorIterable, Shrinkable,
        Sproutable, States,
        connected_components::SccDecomposition,
        model::{Model, ModelEdgeTuple},
    },
};

/// Number of symbols of the alphabet used in the tests.
pub const ALPHABET_SIZE: usize = 3;

/// A single step of a test run. All `usize` fields except `symbol` are selectors.
#[derive(Clone, Debug)]
pub enum Op {
    AddState(u8),
    AddEdge {
        source: usize,
        symbol: usize,
        color: u8,
        target: usize,
    },
    RemoveEdge(usize),
    RemoveState(usize),
    SetStateColor(usize, u8),
    SetEdgeColor(usize, u8),
    RemoveEdgesTo(usize),
    RemoveEdgesFrom(usize),
    RemoveEdgesBetween(usize, usize),
    /// Removes all states not reachable from the selected state (which has to exist).
    TrimFrom(usize),
    /// Compacts the storage, if it can. Renumbers the storage ids.
    Compact,
}

/// The renaming of ids a storage performed when it was compacted.
pub struct Remap<Ts: TransitionSystem> {
    pub state: Box<dyn Fn(Ts::StateIndex) -> Option<Ts::StateIndex>>,
    pub edge: Box<dyn Fn(EdgeId) -> Option<EdgeId>>,
}

fn symbol_char(symbol: usize) -> char {
    (b'a' + (symbol % ALPHABET_SIZE) as u8) as char
}

/// A storage together with the model it is compared against, and the correspondence between the
/// ids handed out by the storage and the ids of the model.
pub struct Harness<Ts: TransitionSystem> {
    ts: Ts,
    model: Model<u8, u8>,
    check: fn(&Ts),
    compact: Option<fn(&mut Ts) -> Remap<Ts>>,
    states: HashMap<usize, Ts::StateIndex>,
    edges: HashMap<usize, EdgeId>,
    /// Storage ids of removed states and edges, to check that compaction maps them to `None`.
    dead_states: Vec<Ts::StateIndex>,
    dead_edges: Vec<EdgeId>,
    /// Number of states ever added, so we can name a state that never existed.
    created_states: usize,
}

impl<Ts> Harness<Ts>
where
    Ts: Sproutable<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8>
        + Shrinkable
        + PredecessorIterable
        + States,
{
    /// Creates a harness around an empty storage. `check` is the consistency check of the storage
    /// and is run after every step.
    pub fn new(ts: Ts, check: fn(&Ts)) -> Self {
        Self::with_model(ts, check, Model::new())
    }

    /// Like [`Self::new`], but compares against a deterministic model, for storages whose
    /// `add_edge` replaces overlapping edges.
    pub fn new_deterministic(ts: Ts, check: fn(&Ts)) -> Self {
        Self::with_model(ts, check, Model::new_deterministic())
    }

    fn with_model(ts: Ts, check: fn(&Ts), model: Model<u8, u8>) -> Self {
        let h = Self {
            ts,
            model,
            check,
            compact: None,
            states: HashMap::new(),
            edges: HashMap::new(),
            dead_states: Vec::new(),
            dead_edges: Vec::new(),
            created_states: 0,
        };
        h.assert_agree();
        h
    }

    /// Enables [`Op::Compact`] with the given way of compacting the storage.
    pub fn with_compaction(mut self, compact: fn(&mut Ts) -> Remap<Ts>) -> Self {
        self.compact = Some(compact);
        self
    }

    /// Applies `ops` one after the other, comparing storage and model after every step.
    pub fn run(mut self, ops: &[Op]) -> Self {
        for op in ops {
            self.step(op);
        }
        self
    }

    /// The state of the model selected by `sel`, or a state that does not exist.
    fn pick_state(&self, sel: usize, allow_missing: bool) -> Option<usize> {
        let live = self.model.states();
        let n = live.len() + usize::from(allow_missing);
        if n == 0 {
            return None;
        }
        Some(live.get(sel % n).copied().unwrap_or(self.created_states))
    }

    /// The edge of the model selected by `sel`, or an id that does not exist.
    fn pick_edge(&self, sel: usize) -> usize {
        let live = self.model.edges();
        let i = sel % (live.len() + 1);
        live.get(i)
            .map(|e| e.0)
            .unwrap_or(live.last().map_or(0, |e| e.0) + 1_000)
    }

    /// The storage id for a state of the model. A state that does not exist in the model is mapped
    /// to an id that is out of range for the storage.
    fn storage_state(&self, q: usize) -> Ts::StateIndex {
        self.states
            .get(&q)
            .copied()
            .or_else(|| Ts::StateIndex::from_dense(1_000_000 + q))
            .expect("storage ids must be dense for this harness")
    }

    fn storage_edge(&self, id: usize) -> EdgeId {
        self.edges.get(&id).copied().unwrap_or(EdgeId(1_000_000))
    }

    fn reverse_state(&self, t: Ts::StateIndex) -> usize {
        *self
            .states
            .iter()
            .find(|(_, s)| **s == t)
            .map(|(m, _)| m)
            .unwrap_or_else(|| panic!("storage returned unknown state {t:?}"))
    }

    /// Forgets the storage ids of edges that no longer exist in the model.
    fn forget_dead_edges(&mut self) {
        let live: Vec<_> = self.model.edges().iter().map(|e| e.0).collect();
        let dead = &mut self.dead_edges;
        self.edges.retain(|id, storage_id| {
            let keep = live.contains(id);
            if !keep {
                dead.push(*storage_id);
            }
            keep
        });
    }

    fn forget_state(&mut self, q: usize) {
        if let Some(storage_id) = self.states.remove(&q) {
            self.dead_states.push(storage_id);
        }
    }

    /// The edge tuple a storage would report for an edge of the model.
    fn storage_tuple(&self, e: &ModelEdgeTuple<u8>) -> EdgeTuple<Ts> {
        (
            self.storage_state(e.1),
            symbol_char(e.2),
            e.3,
            self.storage_state(e.4),
        )
    }

    /// Compares the edges removed from the model with those removed from the storage, ignoring order.
    fn assert_same_removed(
        &self,
        what: &str,
        expected: Option<Vec<ModelEdgeTuple<u8>>>,
        actual: Option<Vec<EdgeTuple<Ts>>>,
    ) {
        let sorted = |v: Vec<EdgeTuple<Ts>>| {
            let mut v = v;
            v.sort();
            v
        };
        assert_eq!(
            expected.map(|v| sorted(v.iter().map(|e| self.storage_tuple(e)).collect())),
            actual.map(sorted),
            "{what} disagrees"
        );
    }

    /// Applies `op` to the storage and the model, checks that the results agree and then compares
    /// the full state of both.
    pub fn step(&mut self, op: &Op) {
        match *op {
            Op::AddState(color) => {
                let expected = self.model.add_state(color);
                let q = self.ts.add_state(color);
                self.created_states += 1;
                self.states.insert(expected, q);
            }
            Op::AddEdge {
                source,
                symbol,
                color,
                target,
            } => {
                let (Some(s), Some(t)) = (
                    self.pick_state(source, false),
                    self.pick_state(target, false),
                ) else {
                    return;
                };
                let id = self
                    .model
                    .add_edge(s, symbol % ALPHABET_SIZE, color, t)
                    .expect("both endpoints exist");
                // a deterministic model may have replaced edges, their ids are dead now
                self.forget_dead_edges();
                let edge: EdgeTuple<Ts> = (
                    self.storage_state(s),
                    symbol_char(symbol),
                    color,
                    self.storage_state(t),
                );
                let storage_id = self.ts.add_edge(edge);
                self.edges.insert(id, storage_id);
            }
            Op::RemoveEdge(sel) => {
                let id = self.pick_edge(sel);
                let expected = self.model.remove_edge(id);
                let actual = self.ts.remove_edge(self.storage_edge(id));
                assert_eq!(
                    expected.map(|(_, s, a, c, t)| (
                        self.storage_state(s),
                        symbol_char(a),
                        c,
                        self.storage_state(t)
                    )),
                    actual,
                    "remove_edge({id}) disagrees"
                );
                self.edges.remove(&id);
            }
            Op::RemoveState(sel) => {
                let Some(q) = self.pick_state(sel, true) else {
                    return;
                };
                let removed = self.model.remove_state(q);
                let actual = self.ts.remove_state(self.storage_state(q));
                assert_eq!(removed, actual, "remove_state({q}) disagrees");
                self.forget_state(q);
                self.forget_dead_edges();
            }
            Op::SetStateColor(sel, color) => {
                let Some(q) = self.pick_state(sel, true) else {
                    return;
                };
                let expected = self.model.set_state_color(q, color);
                let actual = self
                    .ts
                    .state_color_mut(self.storage_state(q))
                    .map(|c| std::mem::replace(c, color));
                assert_eq!(expected, actual, "recoloring state {q} disagrees");
            }
            Op::SetEdgeColor(sel, color) => {
                let id = self.pick_edge(sel);
                let expected = self.model.set_edge_color(id, color);
                let actual = self
                    .ts
                    .edge_color_mut(self.storage_edge(id))
                    .map(|c| std::mem::replace(c, color));
                assert_eq!(expected, actual, "recoloring edge {id} disagrees");
            }
            Op::RemoveEdgesTo(sel) => {
                let Some(q) = self.pick_state(sel, true) else {
                    return;
                };
                let expected = self.model.remove_edges_to(q);
                let actual = self.ts.remove_edges_to(self.storage_state(q));
                self.assert_same_removed(&format!("remove_edges_to({q})"), expected, actual);
                self.forget_dead_edges();
            }
            Op::RemoveEdgesFrom(sel) => {
                let Some(q) = self.pick_state(sel, true) else {
                    return;
                };
                let expected = self.model.remove_edges_from(q);
                let actual = self.ts.remove_edges_from(self.storage_state(q));
                self.assert_same_removed(&format!("remove_edges_from({q})"), expected, actual);
                self.forget_dead_edges();
            }
            Op::RemoveEdgesBetween(source, target) => {
                let (Some(s), Some(t)) =
                    (self.pick_state(source, true), self.pick_state(target, true))
                else {
                    return;
                };
                let expected = self.model.remove_edges_between(s, t);
                let actual = self
                    .ts
                    .remove_edges_between(self.storage_state(s), self.storage_state(t));
                self.assert_same_removed(
                    &format!("remove_edges_between({s}, {t})"),
                    expected,
                    actual,
                );
                self.forget_dead_edges();
            }
            Op::TrimFrom(sel) => {
                let Some(origin) = self.pick_state(sel, false) else {
                    return;
                };
                let removed = self.model.trim_from(origin);
                let mut actual = self.ts.trim_from(self.storage_state(origin));
                actual.sort();
                let mut expected: Vec<_> = removed
                    .iter()
                    .map(|(q, c)| (self.storage_state(*q), *c))
                    .collect();
                expected.sort();
                assert_eq!(expected, actual, "trim_from({origin}) disagrees");
                for (q, _) in removed {
                    self.forget_state(q);
                }
                self.forget_dead_edges();
            }
            Op::Compact => {
                let Some(compact) = self.compact else {
                    return;
                };
                self.compact_storage(compact);
            }
        }
        (self.check)(&self.ts);
        self.assert_agree();
    }

    /// Compacts the storage and follows the renaming of ids.
    fn compact_storage(&mut self, compact: fn(&mut Ts) -> Remap<Ts>) {
        let live_states = self.states.values().copied().collect::<Vec<_>>();
        let live_edges = self.edges.values().copied().collect::<Vec<_>>();
        let remap = compact(&mut self.ts);

        for q in self.dead_states.iter().filter(|q| !live_states.contains(q)) {
            assert_eq!(
                (remap.state)(*q),
                None,
                "removed state {q:?} survived compaction"
            );
        }
        for e in self.dead_edges.iter().filter(|e| !live_edges.contains(e)) {
            assert_eq!(
                (remap.edge)(*e),
                None,
                "removed edge {e:?} survived compaction"
            );
        }
        self.dead_states.clear();
        self.dead_edges.clear();

        let mut by_old_index: Vec<_> = self.states.iter().map(|(m, s)| (*s, *m)).collect();
        by_old_index.sort();
        let mut previous = None;
        for (old, model_id) in by_old_index {
            let new = (remap.state)(old)
                .unwrap_or_else(|| panic!("live state {old:?} lost in compaction"));
            assert!(
                previous < Some(new),
                "compaction does not keep the order of states"
            );
            previous = Some(new);
            self.states.insert(model_id, new);
        }
        let live = self.states.len();
        assert!(
            self.states
                .values()
                .all(|q| q.to_dense().is_none_or(|i| i < live)),
            "states are not consecutive after compaction"
        );

        let mut by_old_id: Vec<_> = self.edges.iter().map(|(m, e)| (*e, *m)).collect();
        by_old_id.sort();
        let mut previous = None;
        for (old, model_id) in by_old_id {
            let new =
                (remap.edge)(old).unwrap_or_else(|| panic!("live edge {old:?} lost in compaction"));
            assert!(
                previous < Some(new),
                "compaction does not keep the order of edges"
            );
            previous = Some(new);
            self.edges.insert(model_id, new);
        }
        let live = self.edges.len();
        assert!(
            self.edges.values().all(|e| (e.0 as usize) < live),
            "edge ids are not consecutive after compaction"
        );
    }

    /// Translates an edge of the storage into the vocabulary of the model.
    fn to_model_edge(
        &self,
        reverse_states: &HashMap<Ts::StateIndex, usize>,
        reverse_edges: &HashMap<EdgeId, usize>,
        e: &crate::ts::EdgeOf<'_, Ts>,
    ) -> ModelEdgeTuple<u8> {
        let id = e.id().expect("storages hand out ids for their edges");
        let symbol = (*e.expression() as u8 - b'a') as usize;
        (
            *reverse_edges
                .get(&id)
                .unwrap_or_else(|| panic!("storage has edge {id:?} the model does not know")),
            *reverse_states
                .get(&e.source())
                .unwrap_or_else(|| panic!("edge from unknown state {:?}", e.source())),
            symbol,
            *e.color(),
            *reverse_states
                .get(&e.target())
                .unwrap_or_else(|| panic!("edge to unknown state {:?}", e.target())),
        )
    }

    /// Compares states, colors, outgoing and incoming edges of the storage with the model.
    pub fn assert_agree(&self) {
        let reverse_states: HashMap<_, _> = self.states.iter().map(|(m, s)| (*s, *m)).collect();
        let reverse_edges: HashMap<_, _> = self.edges.iter().map(|(m, s)| (*s, *m)).collect();

        let mut actual_states: Vec<_> = self
            .ts
            .states()
            .map(|q| {
                *reverse_states
                    .get(&q)
                    .unwrap_or_else(|| panic!("storage has state {q:?} the model does not know"))
            })
            .collect();
        actual_states.sort();
        assert_eq!(self.model.states(), actual_states, "set of states differs");
        assert_eq!(self.model.state_count(), self.ts.state_count());

        for q in self.model.states() {
            let sq = self.storage_state(q);
            assert_eq!(
                self.model.state_color(q),
                self.ts.state_color(sq).map(|c| c.into_owned()),
                "color of state {q} differs"
            );

            let mut out: Vec<_> = self
                .ts
                .edges_from(sq)
                .expect("state exists")
                .map(|e| self.to_model_edge(&reverse_states, &reverse_edges, &e))
                .collect();
            out.sort();
            let expected_out: Vec<_> = {
                let mut v: Vec<_> = self
                    .model
                    .edges_from(q)
                    .unwrap()
                    .into_iter()
                    .map(|e| (e.id, q, e.symbol, e.color, e.target))
                    .collect();
                v.sort();
                v
            };
            assert_eq!(expected_out, out, "edges leaving state {q} differ");

            let mut preds: Vec<_> = self
                .ts
                .predecessors(sq)
                .expect("state exists")
                .map(|e| self.to_model_edge(&reverse_states, &reverse_edges, &e))
                .collect();
            preds.sort();
            assert_eq!(
                self.model.predecessors(q).unwrap(),
                preds,
                "edges entering state {q} differ"
            );
        }

        // a state that never existed is unknown to the storage as well
        let missing = self.storage_state(self.created_states);
        assert!(self.ts.edges_from(missing).is_none());
        assert!(self.ts.predecessors(missing).is_none());
        assert!(self.ts.state_color(missing).is_none());
    }
}

impl<Ts> Harness<Ts>
where
    Ts: Sproutable<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8>
        + Shrinkable
        + PredecessorIterable
        + States,
{
    /// The components of a decomposition in the vocabulary of the model, sorted.
    fn model_sccs(&self, decomposition: &SccDecomposition<'_, Ts>) -> Vec<Vec<usize>> {
        let mut sccs: Vec<Vec<usize>> = decomposition
            .sccs_iter()
            .map(|scc| {
                let mut states: Vec<_> = scc
                    .state_indices()
                    .map(|&q| self.reverse_state(q))
                    .collect();
                states.sort();
                states
            })
            .collect();
        sccs.sort();
        sccs
    }

    /// Compares a subset construction of the storage, started in the states selected by
    /// `origins`, with the model: following a word, the colors of the states of the subset and of
    /// the edges that are taken have to be those of the set of states the model is in.
    pub fn assert_subset_construction_agrees(&self, origins: &[usize], words: &[Vec<usize>]) {
        let states = self.model.states();
        if states.is_empty() {
            return;
        }
        let mut start: Vec<usize> = origins.iter().map(|o| states[o % states.len()]).collect();
        start.sort();
        start.dedup();
        let storage_start: Vec<_> = start.iter().map(|&q| self.storage_state(q)).collect();
        let subset = (&self.ts).subset_construction_from(storage_start);
        let sorted = |mut v: Vec<u8>| {
            v.sort();
            v
        };
        let colors_of = |set: &[usize]| -> Vec<u8> {
            sorted(
                set.iter()
                    .map(|&q| self.model.state_color(q).expect("state exists"))
                    .collect(),
            )
        };

        for word in words {
            let mut model_set = start.clone();
            let mut current = subset.initial();
            for &symbol in word {
                assert_eq!(
                    colors_of(&model_set),
                    sorted(
                        subset
                            .state_color(current)
                            .expect("subset state")
                            .into_owned()
                    ),
                    "state colors of the subset differ after a prefix of {word:?}"
                );
                let edge = subset
                    .edge(current, symbol_char(symbol))
                    .expect("subset construction is complete");
                assert_eq!(
                    self.model.edge_colors_on(&model_set, symbol),
                    sorted(edge.color().clone()),
                    "edge colors of the subset differ on {symbol} in {word:?}"
                );
                current = edge.target();
                model_set = self.model.successors_on(&model_set, symbol);
            }
            assert_eq!(
                colors_of(&model_set),
                sorted(
                    subset
                        .state_color(current)
                        .expect("subset state")
                        .into_owned()
                ),
                "state colors of the subset differ at the end of {word:?}"
            );
            assert_eq!(
                subset.reached_state(word.iter().copied().map(symbol_char).collect::<Vec<_>>()),
                Some(current)
            );
        }
    }

    /// Compares the SCC decompositions of the storage (Tarjan iterative and recursive, and the
    /// variants restricted to what is reachable from a state, also Kosaraju) with the model.
    pub fn assert_sccs_agree(&self) {
        let expected = self.model.sccs();
        let all = self.ts.sccs();
        assert_eq!(expected, self.model_sccs(&all), "sccs() differs");
        assert_eq!(
            expected,
            self.model_sccs(&self.ts.sccs_recursive()),
            "sccs_recursive() differs"
        );

        let mut transient: Vec<_> = all
            .transient_states()
            .map(|q| self.reverse_state(q))
            .collect();
        transient.sort();
        assert_eq!(
            self.model.transient_states(),
            transient,
            "transient states differ"
        );

        for scc in all.sccs_iter() {
            for &q in scc.state_indices() {
                assert_eq!(
                    all.scc_of(q).map(|s| s.first()),
                    Some(scc.first()),
                    "scc_of({q:?}) is not the component containing it"
                );
            }
        }

        for origin in self.model.states() {
            let expected = self.model.sccs_reachable_from(origin);
            let sq = self.storage_state(origin);
            // `reachable_sccs_from` is restricted to the given states, so it is given all that
            // can be reached (for a set that has edges leaving it, building the decomposition
            // panics)
            let reachable: Vec<_> = self
                .model
                .reachable_from(origin)
                .into_iter()
                .map(|q| self.storage_state(q))
                .collect();
            assert_eq!(
                expected,
                self.model_sccs(&self.ts.reachable_sccs_from(reachable)),
                "reachable_sccs_from({origin}) differs"
            );
            assert_eq!(
                expected,
                self.model_sccs(&self.ts.sccs_kosaraju(sq)),
                "sccs_kosaraju({origin}) differs"
            );
        }
    }
}

impl<Ts> Harness<Ts>
where
    Ts: Sproutable<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8>
        + Shrinkable
        + PredecessorIterable
        + Deterministic
        + States,
{
    /// Compares the greatest bisimulations (the partitions that minimization is based on) of
    /// the storage, seen as Moore machine and as Mealy machine, with the classes of the model.
    pub fn assert_minimization_agrees(&self) {
        let to_model = |partition: crate::partition::Partition<Ts::StateIndex>| {
            let mut classes: Vec<Vec<usize>> = (&partition)
                .into_iter()
                .map(|class| {
                    let mut class: Vec<_> = class.iter().map(|&q| self.reverse_state(q)).collect();
                    class.sort();
                    class
                })
                .collect();
            classes.sort();
            classes
        };
        assert_eq!(
            self.model.moore_classes(ALPHABET_SIZE),
            to_model(moore_greatest_bisimulation(&self.ts)),
            "Moore bisimulation differs"
        );
        assert_eq!(
            self.model.mealy_classes(ALPHABET_SIZE),
            to_model(mealy_greatest_bisimulation(&self.ts)),
            "Mealy bisimulation differs"
        );
    }

    /// Compares `edge`, `successor` and runs of a deterministic storage with the model. Every
    /// word is run from every state, and from a state that does not exist.
    pub fn assert_runs_agree(&self, words: &[Vec<usize>]) {
        for q in self.model.states() {
            let sq = self.storage_state(q);
            for symbol in 0..ALPHABET_SIZE {
                let expected = self.model.reach(q, &[symbol]);
                assert!(expected.len() <= 1, "model is not deterministic");
                let actual = self
                    .ts
                    .successor(sq, symbol_char(symbol))
                    .map(|t| self.reverse_state(t));
                assert_eq!(
                    expected.first().copied(),
                    actual,
                    "successor of {q} on {symbol}"
                );
            }
            for word in words {
                let expected = self.model.reach(q, word);
                assert!(expected.len() <= 1, "model is not deterministic");
                let letters: Vec<char> = word.iter().copied().map(symbol_char).collect();
                let actual = self
                    .ts
                    .reached_state_from(sq, letters)
                    .map(|t| self.reverse_state(t));
                assert_eq!(
                    expected.first().copied(),
                    actual,
                    "run from {q} on {word:?}"
                );
            }
        }
        let missing = self.storage_state(self.created_states);
        assert_eq!(
            self.ts.reached_state_from(missing, Vec::<char>::new()),
            None
        );
        assert_eq!(
            self.ts.reached_state_from(missing, vec![symbol_char(0)]),
            None
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::{Compaction, Det, ForAlphabet, LinkedTs};
    use proptest::prelude::*;

    type Linked = LinkedTs<CharAlphabet, u8, u8>;
    type DetLinked = Det<Linked>;

    fn op() -> impl Strategy<Value = Op> {
        let sel = 0usize..16;
        prop_oneof![
            4 => any::<u8>().prop_map(|c| Op::AddState(c % 4)),
            12 => (sel.clone(), 0..ALPHABET_SIZE, 0u8..4, sel.clone()).prop_map(
                |(source, symbol, color, target)| Op::AddEdge { source, symbol, color, target }
            ),
            3 => sel.clone().prop_map(Op::RemoveEdge),
            2 => sel.clone().prop_map(Op::RemoveState),
            2 => (sel.clone(), 0u8..4).prop_map(|(s, c)| Op::SetStateColor(s, c)),
            2 => (sel.clone(), 0u8..4).prop_map(|(s, c)| Op::SetEdgeColor(s, c)),
            1 => sel.clone().prop_map(Op::RemoveEdgesTo),
            1 => sel.clone().prop_map(Op::RemoveEdgesFrom),
            1 => (sel.clone(), sel.clone()).prop_map(|(s, t)| Op::RemoveEdgesBetween(s, t)),
            1 => sel.prop_map(Op::TrimFrom),
            1 => Just(Op::Compact),
        ]
    }

    fn remap(compaction: Compaction) -> Remap<Linked> {
        let for_edges = compaction.clone();
        Remap {
            state: Box::new(move |q| compaction.state(q)),
            edge: Box::new(move |e| for_edges.edge(e)),
        }
    }

    fn compact_linked(ts: &mut Linked) -> Remap<Linked> {
        remap(ts.compact())
    }

    fn compact_det(ts: &mut DetLinked) -> Remap<DetLinked> {
        let compaction = ts.compact();
        let for_edges = compaction.clone();
        Remap {
            state: Box::new(move |q| compaction.state(q)),
            edge: Box::new(move |e| for_edges.edge(e)),
        }
    }

    proptest! {
        #[test]
        fn linked_ts_agrees_with_model(ops in proptest::collection::vec(op(), 0..80)) {
            let ts = Linked::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            Harness::new(ts, Linked::check_consistency)
                .with_compaction(compact_linked)
                .run(&ops);
        }

        #[test]
        fn linked_ts_sccs_agree_with_model(ops in proptest::collection::vec(op(), 0..80)) {
            let ts = Linked::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            Harness::new(ts, Linked::check_consistency)
                .with_compaction(compact_linked)
                .run(&ops)
                .assert_sccs_agree();
        }

        #[test]
        fn det_linked_ts_sccs_agree_with_model(ops in proptest::collection::vec(op(), 0..80)) {
            let ts = DetLinked::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            Harness::new_deterministic(ts, DetLinked::check_consistency)
                .with_compaction(compact_det)
                .run(&ops)
                .assert_sccs_agree();
        }

        #[test]
        fn linked_ts_subset_construction_agrees_with_model(
            ops in proptest::collection::vec(op(), 0..80),
            origins in proptest::collection::vec(0usize..16, 1..4),
            words in proptest::collection::vec(proptest::collection::vec(0..ALPHABET_SIZE, 0..8), 0..8),
        ) {
            let ts = Linked::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            Harness::new(ts, Linked::check_consistency)
                .with_compaction(compact_linked)
                .run(&ops)
                .assert_subset_construction_agrees(&origins, &words);
        }

        #[test]
        fn det_linked_ts_subset_construction_agrees_with_model(
            ops in proptest::collection::vec(op(), 0..80),
            origins in proptest::collection::vec(0usize..16, 1..4),
            words in proptest::collection::vec(proptest::collection::vec(0..ALPHABET_SIZE, 0..8), 0..8),
        ) {
            let ts = DetLinked::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            Harness::new_deterministic(ts, DetLinked::check_consistency)
                .with_compaction(compact_det)
                .run(&ops)
                .assert_subset_construction_agrees(&origins, &words);
        }

        #[test]
        fn det_linked_ts_minimization_agrees_with_model(ops in proptest::collection::vec(op(), 0..80)) {
            let ts = DetLinked::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            Harness::new_deterministic(ts, DetLinked::check_consistency)
                .with_compaction(compact_det)
                .run(&ops)
                .assert_minimization_agrees();
        }

        #[test]
        fn det_linked_ts_runs_agree_with_model(
            ops in proptest::collection::vec(op(), 0..80),
            words in proptest::collection::vec(proptest::collection::vec(0..ALPHABET_SIZE, 0..8), 0..8),
        ) {
            let ts = DetLinked::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            Harness::new_deterministic(ts, DetLinked::check_consistency)
                .with_compaction(compact_det)
                .run(&ops)
                .assert_runs_agree(&words);
        }

        #[test]
        fn det_linked_ts_agrees_with_deterministic_model(ops in proptest::collection::vec(op(), 0..80)) {
            let ts = DetLinked::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            Harness::new_deterministic(ts, DetLinked::check_consistency)
                .with_compaction(compact_det)
                .run(&ops);
        }
    }
}
