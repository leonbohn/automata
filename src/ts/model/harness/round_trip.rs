//! Round trips between storages: collecting a storage into another one (and back) keeps the
//! states, colors and edges up to the renumbering of the states, and keeps the language of the
//! automaton at every state.

use bimap::BiBTreeMap;

use super::*;
use crate::representation::{FromTransitions, IntoTransitions};
use crate::ts::{CompactIdMap, DefaultIdType, DenseId, IdType};
use crate::{
    automaton::{DFA, Equivalence},
    ts::ForAlphabet,
};

/// A storage that can be compared with the model, no matter how its states are numbered.
pub trait Snapshot:
    States<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8> + PredecessorIterable
{
}
impl<T> Snapshot for T where
    T: States<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8> + PredecessorIterable
{
}

/// The DFA that starts in `state` and accepts in the states with an even color.
fn dfa_at<T: Snapshot>(ts: &T, state: T::StateIndex) -> DFA<crate::DTS<CharAlphabet, bool, Void>> {
    ts.map_state_colors(|c| c.is_multiple_of(2))
        .erase_edge_colors()
        .with_initial(state)
        .collect()
}

/// The numbering that collecting applied, as a bijection between the old and the new state indices.
fn bijection<I: IdType, J: DenseId>(map: CompactIdMap<I>) -> BiBTreeMap<I, J> {
    map.states()
        .iter()
        .enumerate()
        .map(|(n, q)| (*q, J::from_usize(n)))
        .collect()
}

impl<Ts> Harness<Ts>
where
    Ts: Sproutable<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8>
        + Shrinkable
        + PredecessorIterable
        + ForAlphabet<CharAlphabet>
        + States,
{
    /// Compares `other` with the model. `renaming` maps the ids of the states in the harness'
    /// storage to those in `other`. Edges are compared by source, symbol, color and target, since
    /// their ids are not preserved.
    fn assert_snapshot_agrees<O: Snapshot>(
        &self,
        other: &O,
        renaming: &BiBTreeMap<Ts::StateIndex, O::StateIndex>,
        what: &str,
    ) {
        let to_model = |o: O::StateIndex| {
            let original = renaming
                .get_by_right(&o)
                .unwrap_or_else(|| panic!("{what}: state {o:?} does not come from the original"));
            self.reverse_state(*original)
        };
        let tuples = |edges: Vec<(usize, usize, u8, usize)>| {
            let mut edges = edges;
            edges.sort();
            edges
        };

        let mut states: Vec<_> = other.states().map(to_model).collect();
        states.sort();
        assert_eq!(self.model.states(), states, "{what}: set of states differs");

        for q in self.model.states() {
            let renamed = *renaming
                .get_by_left(&self.storage_state(q))
                .unwrap_or_else(|| panic!("{what}: state {q} was lost"));
            assert_eq!(
                self.model.state_color(q),
                other.state_color(renamed).map(|c| c.into_owned()),
                "{what}: color of state {q} differs"
            );
            let edge = |e: crate::ts::EdgeOf<'_, O>| {
                (
                    to_model(e.source()),
                    (*e.expression() as u8 - b'a') as usize,
                    *e.color(),
                    to_model(e.target()),
                )
            };
            assert_eq!(
                tuples(
                    self.model
                        .edges_from(q)
                        .expect("state exists")
                        .into_iter()
                        .map(|e| (q, e.symbol, e.color, e.target))
                        .collect()
                ),
                tuples(
                    other
                        .edges_from(renamed)
                        .expect("state exists")
                        .map(edge)
                        .collect()
                ),
                "{what}: edges leaving {q} differ"
            );
            assert_eq!(
                tuples(
                    self.model
                        .predecessors(q)
                        .expect("state exists")
                        .into_iter()
                        .map(|(_, source, symbol, color, _)| (source, symbol, color, q))
                        .collect()
                ),
                tuples(
                    other
                        .predecessors(renamed)
                        .expect("state exists")
                        .map(edge)
                        .collect()
                ),
                "{what}: edges entering {q} differ"
            );
        }
    }

    /// Checks that the DFAs of `other` that start in a state are equivalent to those of the
    /// storage that start in the corresponding state. Only done for a deterministic model, since
    /// collecting a non-deterministic system into a DFA drops edges.
    fn assert_languages_preserved<O: Snapshot>(
        &self,
        other: &O,
        renaming: &BiBTreeMap<Ts::StateIndex, O::StateIndex>,
        what: &str,
    ) {
        if !self.model.is_deterministic() {
            return;
        }
        for q in self.model.states() {
            let original = self.storage_state(q);
            let renamed = *renaming.get_by_left(&original).expect("state was kept");
            assert!(
                Equivalence::of(&dfa_at(&self.ts, original))
                    .and(&dfa_at(other, renamed))
                    .holds(),
                "{what}: the language at state {q} changed"
            );
        }
    }

    /// Collects the storage into `Copy` (with [`IntoTransitions::collect_with_map`]) and
    /// back into a storage of its own type. Both copies have to agree with the model up to the
    /// renumbering of the states and have to preserve the language of every state.
    ///
    /// `Copy` must be able to represent the model, so for a deterministic storage like `Det`
    /// it must be deterministic as well, and for others this should only be called while the
    /// model is deterministic.
    pub fn assert_round_trip_via<Copy>(&self)
    where
        Copy: Sproutable<
                Alphabet = CharAlphabet,
                StateColor = u8,
                EdgeColor = u8,
                StateIndex = DefaultIdType,
            > + ForAlphabet<CharAlphabet>
            + PredecessorIterable
            + States
            + FromTransitions<DefaultIdType>,
        Ts: FromTransitions<DefaultIdType> + TransitionSystem<StateIndex = DefaultIdType>,
    {
        self.reported(|| {
            let name = std::any::type_name::<Copy>();
            let (copy, forward) = (&self.ts).collect_with_map::<Copy>();
            let forward = bijection(forward);
            let what = format!("collecting into {name}");
            self.assert_snapshot_agrees(&copy, &forward, &what);
            self.assert_languages_preserved(&copy, &forward, &what);

            let (back, backward) = (&copy).collect_with_map::<Ts>();
            let backward = bijection(backward);
            let composed: BiBTreeMap<_, _> = forward
                .iter()
                .map(|(original, middle)| {
                    let back = *backward.get_by_left(middle).expect("state was kept");
                    (*original, back)
                })
                .collect();
            let what = format!("collecting into {name} and back");
            self.assert_snapshot_agrees(&back, &composed, &what);
            self.assert_languages_preserved(&back, &composed, &what);
        })
    }
}

impl<Ts> Harness<Ts>
where
    Ts: Sproutable<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8>
        + Shrinkable
        + PredecessorIterable
        + ForAlphabet<CharAlphabet>
        + States,
{
    /// Builds a read-only copy of the storage with `freeze`, which has to number the states in the
    /// order of [`States::states`] of the storage. The copy has to agree with the model up to that
    /// renumbering and has to preserve the language of every state.
    pub fn assert_frozen_agrees<O: Snapshot>(&self, freeze: impl FnOnce(&Ts) -> O) {
        self.reported(|| {
            let frozen = freeze(&self.ts);
            let renaming: BiBTreeMap<_, _> = self.ts.states().zip(frozen.states()).collect();
            assert_eq!(
                renaming.len(),
                self.ts.state_count(),
                "frozen copy has a different number of states"
            );
            self.assert_snapshot_agrees(&frozen, &renaming, "freezing");
            self.assert_languages_preserved(&frozen, &renaming, "freezing");
        })
    }
}
