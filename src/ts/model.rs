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

/// What distinguishes a state during refinement: its current class and, for every symbol, the
/// color of the edge (only for Mealy machines) and the class it leads to, if there is an edge.
type Signature<C> = (usize, Vec<Option<(Option<C>, usize)>>);

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

    /// The states in which a run on `word` starting in `from` can end, in ascending order. The
    /// run takes every edge labelled with the next symbol, so for a deterministic model the result
    /// has at most one element. Empty if `from` does not exist or no run on `word` exists.
    pub fn reach(&self, from: usize, word: &[usize]) -> Vec<usize> {
        self.reach_from_set(&[from], word)
    }

    /// Like [`Self::reach`], but the run may start in any of the states in `from`. States that do
    /// not exist are ignored.
    pub fn reach_from_set(&self, from: &[usize], word: &[usize]) -> Vec<usize> {
        let mut current: Vec<usize> = from
            .iter()
            .copied()
            .filter(|&q| self.contains_state(q))
            .collect();
        current.sort();
        current.dedup();
        for &symbol in word {
            current = self.successors_on(&current, symbol);
        }
        current
    }

    /// The states that can be reached from any of `from` by one edge labelled with `symbol`, in
    /// ascending order.
    pub fn successors_on(&self, from: &[usize], symbol: usize) -> Vec<usize> {
        let mut next = Vec::new();
        for &q in from {
            for e in self.edges_from(q).expect("state exists") {
                if e.symbol == symbol && !next.contains(&e.target) {
                    next.push(e.target);
                }
            }
        }
        next.sort();
        next
    }

    /// The colors of the edges labelled with `symbol` that leave any of `from`, in ascending order.
    pub fn edge_colors_on(&self, from: &[usize], symbol: usize) -> Vec<C>
    where
        C: Ord,
    {
        let mut colors: Vec<C> = from
            .iter()
            .flat_map(|&q| self.edges_from(q).expect("state exists"))
            .filter(|e| e.symbol == symbol)
            .map(|e| e.color)
            .collect();
        colors.sort();
        colors
    }

    /// The states reachable from `origin` (including itself), in ascending order. Computed by
    /// repeating "add all successors" until nothing changes. Empty if `origin` does not exist.
    pub fn reachable_from(&self, origin: usize) -> Vec<usize> {
        self.reachable_within(origin, &self.states())
    }

    /// Like [`Self::reachable_from`], but only the states in `allowed` may be visited. Empty if
    /// `origin` does not exist or is not allowed.
    pub fn reachable_within(&self, origin: usize, allowed: &[usize]) -> Vec<usize> {
        if !self.contains_state(origin) || !allowed.contains(&origin) {
            return Vec::new();
        }
        let mut reached = vec![origin];
        loop {
            let mut grew = false;
            for (_, source, _, _, target) in self.edges() {
                if reached.contains(&source)
                    && allowed.contains(&target)
                    && !reached.contains(&target)
                {
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

    /// The coarsest partition of the states such that states in one class have the same state
    /// color and, for every symbol, either no edge or edges into the same class. Computed by
    /// refining the classes by color until nothing changes. Classes and their members are sorted.
    ///
    /// # Panics
    /// If the model is not deterministic.
    pub fn moore_classes(&self, symbols: usize) -> Vec<Vec<usize>>
    where
        Q: PartialEq,
        C: PartialEq,
    {
        self.refine_classes(symbols, true)
    }

    /// The coarsest partition of the states such that, for every symbol, states in one class have
    /// either no edge or edges with the same color into the same class. The state colors are
    /// ignored.
    ///
    /// # Panics
    /// If the model is not deterministic.
    pub fn mealy_classes(&self, symbols: usize) -> Vec<Vec<usize>>
    where
        Q: PartialEq,
        C: PartialEq,
    {
        self.refine_classes(symbols, false)
    }

    fn refine_classes(&self, symbols: usize, by_state_color: bool) -> Vec<Vec<usize>>
    where
        Q: PartialEq,
        C: PartialEq,
    {
        let states = self.states();
        // the class of every state, indexed by position in `states`
        let mut class = vec![0usize; states.len()];
        if by_state_color {
            let mut seen: Vec<Q> = Vec::new();
            for (i, &q) in states.iter().enumerate() {
                let color = self.state_color(q).expect("state exists");
                class[i] = match seen.iter().position(|c| *c == color) {
                    Some(k) => k,
                    None => {
                        seen.push(color);
                        seen.len() - 1
                    }
                };
            }
        }
        loop {
            let class_of = |q: usize| class[states.iter().position(|&p| p == q).unwrap()];
            let mut signatures: Vec<Signature<C>> = Vec::new();
            let mut next = vec![0usize; states.len()];
            for (i, &q) in states.iter().enumerate() {
                let outgoing = self.edges_from(q).expect("state exists");
                let signature: Vec<_> = (0..symbols)
                    .map(|symbol| {
                        let mut on_symbol = outgoing.iter().filter(|e| e.symbol == symbol);
                        let edge = on_symbol.next();
                        assert!(on_symbol.next().is_none(), "model is not deterministic");
                        edge.map(|e| {
                            let color = (!by_state_color).then(|| e.color.clone());
                            (color, class_of(e.target))
                        })
                    })
                    .collect();
                let entry = (class[i], signature);
                next[i] = match signatures.iter().position(|s| *s == entry) {
                    Some(k) => k,
                    None => {
                        signatures.push(entry);
                        signatures.len() - 1
                    }
                };
            }
            let before = class.iter().max().map_or(0, |m| m + 1);
            let after = signatures.len();
            class = next;
            if before == after {
                break;
            }
        }
        let mut classes: Vec<Vec<usize>> = Vec::new();
        for k in 0..class.iter().max().map_or(0, |m| m + 1) {
            classes.push(
                states
                    .iter()
                    .zip(&class)
                    .filter(|(_, c)| **c == k)
                    .map(|(q, _)| *q)
                    .collect(),
            );
        }
        classes.sort();
        classes
    }

    /// The model as text, one line per state: its color and the edges leaving it as
    /// `symbol/color -> target`.
    pub fn describe(&self) -> String
    where
        Q: std::fmt::Debug,
        C: std::fmt::Debug,
    {
        let mut text = String::new();
        for q in self.states() {
            let (color, edges) = self.states[q].as_ref().expect("state exists");
            let edges: Vec<_> = edges
                .iter()
                .map(|e| {
                    format!(
                        "{}/{:?} -> q{}",
                        (b'a' + e.symbol as u8) as char,
                        e.color,
                        e.target
                    )
                })
                .collect();
            text += &format!("  q{q} (color {color:?}): {}\n", edges.join(", "));
        }
        if text.is_empty() {
            text = "  (no states)\n".to_string();
        }
        text
    }

    /// Whether no state has two edges with the same symbol.
    pub fn is_deterministic(&self) -> bool {
        self.states().into_iter().all(|q| {
            let edges = self.edges_from(q).expect("state exists");
            edges
                .iter()
                .enumerate()
                .all(|(i, e)| edges[i + 1..].iter().all(|f| f.symbol != e.symbol))
        })
    }

    /// The edge leaving `state` with `symbol`, in a deterministic model.
    fn edge_on(&self, state: usize, symbol: usize) -> Option<ModelEdge<C>> {
        let mut edges = self
            .edges_from(state)?
            .into_iter()
            .filter(|e| e.symbol == symbol);
        let edge = edges.next();
        assert!(edges.next().is_none(), "model is not deterministic");
        edge
    }

    /// Whether the DFAs that start in `p` and `q` accept the same words, where a state is
    /// accepting if `accepting` holds for its color, and a run that cannot continue is rejecting.
    /// All pairs of states that the two can be in after reading the same word are explored, a
    /// missing state counts as a rejecting sink (`None`).
    pub fn language_equivalent(
        &self,
        p: usize,
        q: usize,
        symbols: usize,
        accepting: impl Fn(&Q) -> bool,
    ) -> bool {
        let accepts = |state: Option<usize>| {
            state.is_some_and(|s| accepting(&self.state_color(s).expect("state exists")))
        };
        let mut seen = vec![(Some(p), Some(q))];
        let mut todo = 0;
        while todo < seen.len() {
            let (a, b) = seen[todo];
            todo += 1;
            if accepts(a) != accepts(b) {
                return false;
            }
            for symbol in 0..symbols {
                let next = (
                    a.and_then(|s| self.edge_on(s, symbol)).map(|e| e.target),
                    b.and_then(|s| self.edge_on(s, symbol)).map(|e| e.target),
                );
                if !seen.contains(&next) {
                    seen.push(next);
                }
            }
        }
        true
    }

    /// Whether the Moore machines that start in `p` and `q` have the same state colors on every
    /// word that can be read from both.
    pub fn moore_compatible(&self, p: usize, q: usize, symbols: usize) -> bool
    where
        Q: PartialEq,
    {
        let mut seen = vec![(p, q)];
        let mut todo = 0;
        while todo < seen.len() {
            let (a, b) = seen[todo];
            todo += 1;
            if self.state_color(a) != self.state_color(b) {
                return false;
            }
            for symbol in 0..symbols {
                if let (Some(x), Some(y)) = (self.edge_on(a, symbol), self.edge_on(b, symbol))
                    && !seen.contains(&(x.target, y.target))
                {
                    seen.push((x.target, y.target));
                }
            }
        }
        true
    }

    /// Whether the Mealy machines that start in `p` and `q` read the same words and produce the
    /// same edge colors on them: at every pair of states reached on a common word, the same
    /// symbols have an edge and the edges have the same colors.
    pub fn mealy_equivalent(&self, p: usize, q: usize, symbols: usize) -> bool
    where
        C: PartialEq,
    {
        let mut seen = vec![(p, q)];
        let mut todo = 0;
        while todo < seen.len() {
            let (a, b) = seen[todo];
            todo += 1;
            for symbol in 0..symbols {
                match (self.edge_on(a, symbol), self.edge_on(b, symbol)) {
                    (None, None) => {}
                    (Some(x), Some(y)) => {
                        if x.color != y.color {
                            return false;
                        }
                        if !seen.contains(&(x.target, y.target)) {
                            seen.push((x.target, y.target));
                        }
                    }
                    _ => return false,
                }
            }
        }
        true
    }

    /// The strongly connected components: two states are in the same one iff each is reachable
    /// from the other. Every component is sorted, and the components are sorted by their smallest
    /// state.
    pub fn sccs(&self) -> Vec<Vec<usize>> {
        self.sccs_within(&self.states())
    }

    /// The strongly connected components of the part of the model that consists of the states in
    /// `allowed` and the edges between them.
    pub fn sccs_within(&self, allowed: &[usize]) -> Vec<Vec<usize>> {
        let mut allowed = allowed.to_vec();
        allowed.sort();
        let mut sccs: Vec<Vec<usize>> = Vec::new();
        for &q in &allowed {
            if sccs.iter().any(|scc| scc.contains(&q)) {
                continue;
            }
            let scc = self
                .reachable_within(q, &allowed)
                .into_iter()
                .filter(|&p| self.reachable_within(p, &allowed).contains(&q))
                .collect();
            sccs.push(scc);
        }
        sccs
    }

    /// The strongly connected components that contain a state reachable from one of `origins`.
    pub fn sccs_reachable_from(&self, origins: &[usize]) -> Vec<Vec<usize>> {
        let reachable: Vec<usize> = origins
            .iter()
            .flat_map(|&origin| self.reachable_from(origin))
            .collect();
        self.sccs()
            .into_iter()
            .filter(|scc| reachable.contains(&scc[0]))
            .collect()
    }

    /// The states that cannot reach themselves by reading a non-empty word, in ascending order.
    pub fn transient_states(&self) -> Vec<usize> {
        self.states()
            .into_iter()
            .filter(|&q| {
                !self
                    .edges_from(q)
                    .expect("state exists")
                    .iter()
                    .any(|e| self.reach_any(e.target, q))
            })
            .collect()
    }

    /// Whether `to` is reachable from `from` by reading a (possibly empty) word.
    fn reach_any(&self, from: usize, to: usize) -> bool {
        self.reachable_from(from).contains(&to)
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
    fn reach_follows_words() {
        let mut m = Model::<(), ()>::new();
        let q: Vec<_> = (0..3).map(|_| m.add_state(())).collect();
        m.add_edge(q[0], 0, (), q[1]);
        m.add_edge(q[0], 0, (), q[2]);
        m.add_edge(q[1], 1, (), q[0]);
        assert_eq!(m.reach(q[0], &[]), vec![q[0]]);
        assert_eq!(m.reach(q[0], &[0]), vec![q[1], q[2]]);
        assert_eq!(m.reach(q[0], &[0, 1]), vec![q[0]]);
        assert_eq!(m.reach(q[0], &[1]), vec![]);
        assert_eq!(m.reach(9, &[]), vec![]);
    }

    #[test]
    fn sccs_and_transient_states() {
        let mut m = Model::<(), ()>::new();
        let q: Vec<_> = (0..5).map(|_| m.add_state(())).collect();
        m.add_edge(q[0], 0, (), q[1]);
        m.add_edge(q[1], 0, (), q[0]);
        m.add_edge(q[1], 1, (), q[2]);
        m.add_edge(q[2], 0, (), q[2]);
        m.add_edge(q[3], 0, (), q[0]);
        assert_eq!(
            m.sccs(),
            vec![vec![q[0], q[1]], vec![q[2]], vec![q[3]], vec![q[4]]]
        );
        assert_eq!(
            m.sccs_reachable_from(&[q[1]]),
            vec![vec![q[0], q[1]], vec![q[2]]]
        );
        assert_eq!(m.transient_states(), vec![q[3], q[4]]);
    }

    #[test]
    fn reach_from_sets() {
        let mut m = Model::<u8, u8>::new();
        let q: Vec<_> = (0..3).map(|c| m.add_state(c)).collect();
        m.add_edge(q[0], 0, 5, q[1]);
        m.add_edge(q[2], 0, 4, q[1]);
        m.add_edge(q[2], 0, 3, q[2]);
        assert_eq!(m.reach_from_set(&[q[2], q[0], 9], &[0]), vec![q[1], q[2]]);
        assert_eq!(m.reach_from_set(&[q[0], q[0]], &[]), vec![q[0]]);
        assert_eq!(m.edge_colors_on(&[q[0], q[2]], 0), vec![3, 4, 5]);
        assert_eq!(m.edge_colors_on(&[q[1]], 0), Vec::<u8>::new());
    }

    #[test]
    fn minimization_classes() {
        let mut m = Model::<u8, u8>::new();
        let q: Vec<_> = [0, 0, 1, 0].iter().map(|&c| m.add_state(c)).collect();
        // 0 and 1 behave the same, 3 has no edge so it differs from them
        m.add_edge(q[0], 0, 7, q[2]);
        m.add_edge(q[1], 0, 8, q[2]);
        m.add_edge(q[2], 0, 7, q[2]);
        assert_eq!(
            m.moore_classes(1),
            vec![vec![q[0], q[1]], vec![q[2]], vec![q[3]]]
        );
        // for Mealy machines the edge colors tell 0 and 1 apart, 2 and 0 agree on the edge color
        assert_eq!(
            m.mealy_classes(1),
            vec![vec![q[0], q[2]], vec![q[1]], vec![q[3]]]
        );
    }

    #[test]
    fn equivalence_of_states() {
        let mut m = Model::<u8, u8>::new();
        let q: Vec<_> = [1, 1, 0, 1].iter().map(|&c| m.add_state(c)).collect();
        m.add_edge(q[0], 0, 5, q[2]);
        m.add_edge(q[1], 0, 6, q[2]);
        m.add_edge(q[2], 0, 5, q[2]);
        let even = |c: &u8| *c == 0;
        // q[3] has no edge but accepts nothing different from q[0] on the empty word
        assert!(m.language_equivalent(q[0], q[1], 1, even));
        assert!(!m.language_equivalent(q[0], q[3], 1, even));
        assert!(m.moore_compatible(q[0], q[3], 1));
        assert!(!m.moore_compatible(q[0], q[2], 1));
        assert!(!m.mealy_equivalent(q[0], q[1], 1));
        assert!(!m.mealy_equivalent(q[0], q[3], 1));
        assert!(m.mealy_equivalent(q[0], q[0], 1));
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
