use crate::TransitionSystem;
use crate::alphabet::{Alphabet, Expression};
use crate::ts::EdgeOf;
use crate::ts::{Deterministic, SymbolOf};

/// Specialized version of an iterator over the edges leaving a specific state of a **deterministic**
/// transition system.
pub struct DeterministicEdgesFrom<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    state: Ts::StateIndex,
    symbols: <Ts::Alphabet as Alphabet>::Universe<'a>,
}

impl<'a, Ts: Deterministic> Iterator for DeterministicEdgesFrom<'a, Ts> {
    type Item = EdgeOf<'a, Ts>;
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
    symbols: std::vec::IntoIter<SymbolOf<D>>,
    target: Option<D::StateIndex>,
    color: Option<D::EdgeColor>,
    source: D::StateIndex,
}

impl<'a, D: TransitionSystem + 'a> Iterator for TransitionsFrom<'a, D> {
    type Item = (D::StateIndex, SymbolOf<D>, D::EdgeColor, D::StateIndex);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(sym) = self.symbols.next() {
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
                    let color = t.color().clone();
                    // an expression usually stands for few symbols, so this seldom allocates
                    self.symbols = it.collect::<Vec<_>>().into_iter();
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
    /// from which the transitions should be taken. Returns `None` if the state does not exist.
    pub fn new(det: &'a D, state: D::StateIndex) -> Option<Self> {
        let edges = det.edges_from(state)?;

        Some(Self {
            edges,
            symbols: Vec::new().into_iter(),

            target: None,
            color: None,
            source: state,
        })
    }
}
