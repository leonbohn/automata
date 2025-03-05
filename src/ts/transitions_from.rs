use crate::TransitionSystem;
use crate::ts::{Deterministic, EdgeExpression, IsEdge, SymbolOf};
use automata_core::alphabet::{Alphabet, Expression};

/// Specialized version of an iterator over the edges leaving a specific state of a **deterministic**
/// transition system.
pub struct DeterministicEdgesFrom<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    state: Ts::StateIndex,
    symbols: <Ts::Alphabet as Alphabet>::Universe<'a>,
}

impl<'a, Ts: Deterministic> Iterator for DeterministicEdgesFrom<'a, Ts> {
    type Item = Ts::EdgeRef<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        self.symbols
            .next()
            .and_then(|sym| self.ts.edge(self.state, sym))
    }
}

impl<'a, Ts: TransitionSystem> DeterministicEdgesFrom<'a, Ts> {
    /// Creates a new instance from the given components.
    pub fn new(ts: &'a Ts, state: Ts::StateIndex) -> Self {
        Self {
            ts,
            state,
            symbols: ts.alphabet().universe(),
        }
    }
}

/// Through this struct, we enable iterating over all transitions that leave a given state of
/// a transition system.
pub struct TransitionsFrom<'a, D: TransitionSystem + 'a> {
    edges: D::EdgesFromIter<'a>,
    symbols: Option<<EdgeExpression<D> as Expression>::SymbolsIter<'a>>,
    target: Option<D::StateIndex>,
    color: Option<D::EdgeColor>,
    source: D::StateIndex,
}

impl<'a, D: TransitionSystem + 'a> Iterator for TransitionsFrom<'a, D> {
    type Item = (D::StateIndex, SymbolOf<D>, D::EdgeColor, D::StateIndex);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(sym) = self.symbols.as_mut().and_then(|it| it.next()) {
            return Some((
                self.source,
                sym,
                self.color.clone().unwrap(),
                self.target.unwrap(),
            ));
        } else {
            for t in self.edges.by_ref() {
                let mut it = t.expression().symbols();
                if let Some(sym) = it.next() {
                    let target = t.target();
                    let color = t.color();
                    self.symbols = Some(it);
                    self.color = Some(color.clone());
                    self.target = Some(target);
                    return Some((self.source, sym, color.clone(), target));
                }
            }
        }
        None
    }
}

impl<'a, D: TransitionSystem + 'a> TransitionsFrom<'a, D> {
    /// Creates a new instance from a reference to a transition system and the index of the state
    /// from which the transitions should be taken.
    pub fn new(det: &'a D, state: D::StateIndex) -> Self {
        let Some(edges) = det.edges_from(state) else {
            panic!(
                "We should at least get an iterator. Probably the state {state:?} does not exist.",
            );
        };

        Self {
            edges,
            symbols: None,

            target: None,
            color: None,
            source: state,
        }
    }
}
