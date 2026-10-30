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
    ts::{
        EdgeId, EdgeTuple, IdType, PredecessorIterable, Shrinkable, Sproutable, States,
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
    states: HashMap<usize, Ts::StateIndex>,
    edges: HashMap<usize, EdgeId>,
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
            states: HashMap::new(),
            edges: HashMap::new(),
            created_states: 0,
        };
        h.assert_agree();
        h
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

    /// Forgets the storage ids of edges that no longer exist in the model.
    fn forget_dead_edges(&mut self) {
        let live: Vec<_> = self.model.edges().iter().map(|e| e.0).collect();
        self.edges.retain(|id, _| live.contains(id));
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
                self.states.remove(&q);
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
        }
        (self.check)(&self.ts);
        self.assert_agree();
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

/// Applies `ops` one after the other, comparing storage and model after every step.
pub fn run_ops<Ts>(ts: Ts, check: fn(&Ts), ops: &[Op])
where
    Ts: Sproutable<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8>
        + Shrinkable
        + PredecessorIterable
        + States,
{
    let mut harness = Harness::new(ts, check);
    for op in ops {
        harness.step(op);
    }
}

/// Like [`run_ops`] for storages that are deterministic.
pub fn run_ops_deterministic<Ts>(ts: Ts, check: fn(&Ts), ops: &[Op])
where
    Ts: Sproutable<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8>
        + Shrinkable
        + PredecessorIterable
        + States,
{
    let mut harness = Harness::new_deterministic(ts, check);
    for op in ops {
        harness.step(op);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::{Det, ForAlphabet, LinkedTs};
    use proptest::prelude::*;

    fn op() -> impl Strategy<Value = Op> {
        let sel = 0usize..16;
        prop_oneof![
            2 => any::<u8>().prop_map(|c| Op::AddState(c % 4)),
            6 => (sel.clone(), 0..ALPHABET_SIZE, 0u8..4, sel.clone()).prop_map(
                |(source, symbol, color, target)| Op::AddEdge { source, symbol, color, target }
            ),
            2 => sel.clone().prop_map(Op::RemoveEdge),
            1 => sel.clone().prop_map(Op::RemoveState),
            1 => (sel.clone(), 0u8..4).prop_map(|(s, c)| Op::SetStateColor(s, c)),
            1 => (sel, 0u8..4).prop_map(|(s, c)| Op::SetEdgeColor(s, c)),
        ]
    }

    proptest! {
        #[test]
        fn linked_ts_agrees_with_model(ops in proptest::collection::vec(op(), 0..80)) {
            let ts = LinkedTs::<CharAlphabet, u8, u8>::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            run_ops(ts, LinkedTs::check_consistency, &ops);
        }

        #[test]
        fn det_linked_ts_agrees_with_deterministic_model(ops in proptest::collection::vec(op(), 0..80)) {
            let ts = Det::<LinkedTs<CharAlphabet, u8, u8>>::for_alphabet(CharAlphabet::of_size(ALPHABET_SIZE));
            run_ops_deterministic(ts, Det::check_consistency, &ops);
        }
    }
}
