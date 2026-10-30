//! A deliberately naive model of a transition system, used as the reference in model-based tests
//! of the storages (#53). Everything here favours being obviously correct over being fast: states
//! are a `Vec`, edges are plain lists, and every query is a linear scan.
//!
//! The model is independent of the library traits on purpose, so that it cannot share a bug with
//! the code it checks. Symbols are plain `usize`s, edges are labelled with exactly one symbol.
//! States and edges have stable identifiers that are never reused after removal, just like in
//! the real storages.

#[cfg(test)]
mod harness;

/// An edge of the model, stored with the state it starts in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ModelEdge<C> {
    /// Identifier of the edge, unique within the model for its whole lifetime.
    pub id: usize,
    /// The symbol this edge is labelled with.
    pub symbol: usize,
    /// The color of the edge.
    pub color: C,
    /// The state the edge leads to.
    pub target: usize,
}

/// A fully expanded edge `source --symbol:color--> target` together with its identifier.
pub type ModelEdgeTuple<C> = (usize, usize, usize, C, usize);

/// Naive transition system with state colors `Q` and edge colors `C`.
///
/// `states[i]` is `None` once state `i` has been removed, otherwise it holds the color of the
/// state and the list of edges leaving it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Model<Q, C> {
    states: Vec<Option<(Q, Vec<ModelEdge<C>>)>>,
    next_edge_id: usize,
    deterministic: bool,
}

impl<Q: Clone, C: Clone> Model<Q, C> {
    /// Creates an empty model.
    pub fn new() -> Self {
        Self {
            states: Vec::new(),
            next_edge_id: 0,
            deterministic: false,
        }
    }

    /// Creates an empty model that is deterministic: adding an edge replaces the edges that leave
    /// the same state with the same symbol, like `Det` does.
    pub fn new_deterministic() -> Self {
        Self {
            deterministic: true,
            ..Self::new()
        }
    }

    /// Adds a state with the given color and returns its index.
    pub fn add_state(&mut self, color: Q) -> usize {
        self.states.push(Some((color, Vec::new())));
        self.states.len() - 1
    }

    /// Adds an edge and returns its id (in a deterministic model, edges with the same source and
    /// symbol are removed first), or `None` if `source` or `target` does not exist.
    pub fn add_edge(
        &mut self,
        source: usize,
        symbol: usize,
        color: C,
        target: usize,
    ) -> Option<usize> {
        if !self.contains_state(source) || !self.contains_state(target) {
            return None;
        }
        let id = self.next_edge_id;
        self.next_edge_id += 1;
        let (_, edges) = self.states[source].as_mut()?;
        if self.deterministic {
            edges.retain(|e| e.symbol != symbol);
        }
        edges.push(ModelEdge {
            id,
            symbol,
            color,
            target,
        });
        Some(id)
    }

    /// Removes the edge with the given id and returns it, or `None` if there is no such edge.
    pub fn remove_edge(&mut self, id: usize) -> Option<ModelEdgeTuple<C>> {
        for (source, slot) in self.states.iter_mut().enumerate() {
            let Some((_, edges)) = slot else { continue };
            if let Some(pos) = edges.iter().position(|e| e.id == id) {
                let e = edges.remove(pos);
                return Some((e.id, source, e.symbol, e.color, e.target));
            }
        }
        None
    }

    /// Removes a state together with all edges leaving or entering it. Returns the color of the
    /// state, or `None` if it does not exist.
    pub fn remove_state(&mut self, state: usize) -> Option<Q> {
        let (color, _) = self.states.get_mut(state)?.take()?;
        for slot in self.states.iter_mut().flatten() {
            slot.1.retain(|e| e.target != state);
        }
        Some(color)
    }

    /// Removes all edges entering `state` and returns them, or `None` if the state does not exist.
    pub fn remove_edges_to(&mut self, state: usize) -> Option<Vec<ModelEdgeTuple<C>>> {
        let ids: Vec<_> = self.predecessors(state)?.iter().map(|e| e.0).collect();
        Some(
            ids.into_iter()
                .filter_map(|id| self.remove_edge(id))
                .collect(),
        )
    }

    /// Removes all edges leaving `state` and returns them, or `None` if the state does not exist.
    pub fn remove_edges_from(&mut self, state: usize) -> Option<Vec<ModelEdgeTuple<C>>> {
        let ids: Vec<_> = self.edges_from(state)?.iter().map(|e| e.id).collect();
        Some(
            ids.into_iter()
                .filter_map(|id| self.remove_edge(id))
                .collect(),
        )
    }

    /// Removes all edges from `source` to `target` and returns them, or `None` if one of the two
    /// states does not exist.
    pub fn remove_edges_between(
        &mut self,
        source: usize,
        target: usize,
    ) -> Option<Vec<ModelEdgeTuple<C>>> {
        if !self.contains_state(target) {
            return None;
        }
        let ids: Vec<_> = self
            .edges_from(source)?
            .iter()
            .filter(|e| e.target == target)
            .map(|e| e.id)
            .collect();
        Some(
            ids.into_iter()
                .filter_map(|id| self.remove_edge(id))
                .collect(),
        )
    }

    /// The states reachable from `origin` (including itself), in ascending order. Computed by
    /// repeating "add all successors" until nothing changes. Empty if `origin` does not exist.
    pub fn reachable_from(&self, origin: usize) -> Vec<usize> {
        if !self.contains_state(origin) {
            return Vec::new();
        }
        let mut reached = vec![origin];
        loop {
            let mut grew = false;
            for (_, source, _, _, target) in self.edges() {
                if reached.contains(&source) && !reached.contains(&target) {
                    reached.push(target);
                    grew = true;
                }
            }
            if !grew {
                reached.sort();
                return reached;
            }
        }
    }

    /// Removes every state that is not reachable from `origin` and returns them with their colors
    /// in ascending order.
    ///
    /// # Panics
    /// If `origin` does not exist.
    pub fn trim_from(&mut self, origin: usize) -> Vec<(usize, Q)> {
        assert!(self.contains_state(origin));
        let reachable = self.reachable_from(origin);
        let mut removed = Vec::new();
        for q in self.states() {
            if !reachable.contains(&q) {
                removed.push((q, self.remove_state(q).expect("state exists")));
            }
        }
        removed
    }

    /// Replaces the color of a state and returns the old one, or `None` if it does not exist.
    pub fn set_state_color(&mut self, state: usize, color: Q) -> Option<Q> {
        let (old, _) = self.states.get_mut(state)?.as_mut()?;
        Some(std::mem::replace(old, color))
    }

    /// Replaces the color of an edge and returns the old one, or `None` if it does not exist.
    pub fn set_edge_color(&mut self, id: usize, color: C) -> Option<C> {
        self.states
            .iter_mut()
            .flatten()
            .flat_map(|(_, edges)| edges.iter_mut())
            .find(|e| e.id == id)
            .map(|e| std::mem::replace(&mut e.color, color))
    }

    /// Whether `state` exists.
    pub fn contains_state(&self, state: usize) -> bool {
        matches!(self.states.get(state), Some(Some(_)))
    }

    /// Indices of all existing states in ascending order.
    pub fn states(&self) -> Vec<usize> {
        (0..self.states.len())
            .filter(|&q| self.contains_state(q))
            .collect()
    }

    /// The number of existing states.
    pub fn state_count(&self) -> usize {
        self.states().len()
    }

    /// The color of `state`, or `None` if it does not exist.
    pub fn state_color(&self, state: usize) -> Option<Q> {
        self.states.get(state)?.as_ref().map(|(q, _)| q.clone())
    }

    /// The edges leaving `state` in insertion order, or `None` if it does not exist.
    pub fn edges_from(&self, state: usize) -> Option<Vec<ModelEdge<C>>> {
        self.states
            .get(state)?
            .as_ref()
            .map(|(_, edges)| edges.clone())
    }

    /// All edges of the model, ordered by id.
    pub fn edges(&self) -> Vec<ModelEdgeTuple<C>> {
        let mut all: Vec<_> = self
            .states
            .iter()
            .enumerate()
            .filter_map(|(source, slot)| slot.as_ref().map(|(_, edges)| (source, edges)))
            .flat_map(|(source, edges)| {
                edges
                    .iter()
                    .map(move |e| (e.id, source, e.symbol, e.color.clone(), e.target))
            })
            .collect();
        all.sort_by_key(|e| e.0);
        all
    }

    /// The edges entering `state`, ordered by id, or `None` if it does not exist.
    pub fn predecessors(&self, state: usize) -> Option<Vec<ModelEdgeTuple<C>>> {
        if !self.contains_state(state) {
            return None;
        }
        Some(self.edges().into_iter().filter(|e| e.4 == state).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_and_query() {
        let mut m = Model::<bool, u8>::new();
        let q0 = m.add_state(false);
        let q1 = m.add_state(true);
        let e0 = m.add_edge(q0, 0, 7, q1).unwrap();
        let e1 = m.add_edge(q1, 1, 8, q0).unwrap();
        assert_eq!(m.states(), vec![q0, q1]);
        assert_eq!(m.state_color(q1), Some(true));
        assert_eq!(m.edges(), vec![(e0, q0, 0, 7, q1), (e1, q1, 1, 8, q0)]);
        assert_eq!(m.predecessors(q0), Some(vec![(e1, q1, 1, 8, q0)]));
        assert_eq!(m.add_edge(q0, 0, 0, 5), None);
        assert_eq!(m.edges_from(q0).unwrap().len(), 1);
        assert_eq!(m.edges_from(5), None);
    }

    #[test]
    fn remove_state_removes_incident_edges_and_never_reuses_ids() {
        let mut m = Model::<(), ()>::new();
        let q0 = m.add_state(());
        let q1 = m.add_state(());
        m.add_edge(q0, 0, (), q1);
        m.add_edge(q1, 0, (), q0);
        m.add_edge(q0, 1, (), q0);
        assert_eq!(m.remove_state(q1), Some(()));
        assert_eq!(m.remove_state(q1), None);
        assert_eq!(m.edges().len(), 1);
        assert_eq!(m.state_count(), 1);
        assert_eq!(m.add_state(()), 2);
        assert_eq!(m.add_edge(q0, 0, (), q1), None);
    }

    #[test]
    fn deterministic_model_replaces_overlapping_edges() {
        let mut m = Model::<(), u8>::new_deterministic();
        let q = m.add_state(());
        let a = m.add_edge(q, 0, 1, q).unwrap();
        let b = m.add_edge(q, 1, 2, q).unwrap();
        let c = m.add_edge(q, 0, 3, q).unwrap();
        assert_eq!(m.edges(), vec![(b, q, 1, 2, q), (c, q, 0, 3, q)]);
        assert_eq!(m.remove_edge(a), None);
    }

    #[test]
    fn bulk_removal_and_trim() {
        let mut m = Model::<u8, ()>::new();
        let q: Vec<_> = (0..4).map(|c| m.add_state(c)).collect();
        m.add_edge(q[0], 0, (), q[1]);
        m.add_edge(q[0], 1, (), q[1]);
        m.add_edge(q[1], 0, (), q[1]);
        m.add_edge(q[2], 0, (), q[3]);
        assert_eq!(m.reachable_from(q[0]), vec![q[0], q[1]]);
        assert_eq!(m.remove_edges_between(q[0], q[1]).unwrap().len(), 2);
        assert_eq!(m.remove_edges_between(q[0], 9), None);
        assert_eq!(m.remove_edges_to(q[1]).unwrap().len(), 1);
        assert_eq!(m.remove_edges_from(q[2]).unwrap().len(), 1);
        assert_eq!(m.remove_edges_from(9), None);
        assert_eq!(m.trim_from(q[0]), vec![(q[1], 1), (q[2], 2), (q[3], 3)]);
        assert_eq!(m.states(), vec![q[0]]);
    }

    #[test]
    fn remove_edge_and_recolor() {
        let mut m = Model::<u8, u8>::new();
        let q = m.add_state(1);
        let a = m.add_edge(q, 0, 2, q).unwrap();
        let b = m.add_edge(q, 0, 3, q).unwrap();
        assert_eq!(m.set_state_color(q, 9), Some(1));
        assert_eq!(m.set_edge_color(b, 4), Some(3));
        assert_eq!(m.remove_edge(a), Some((a, q, 0, 2, q)));
        assert_eq!(m.remove_edge(a), None);
        assert_eq!(m.edges(), vec![(b, q, 0, 4, q)]);
        assert_eq!(m.set_edge_color(a, 0), None);
    }
}
