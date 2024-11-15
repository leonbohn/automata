use std::borrow::Borrow;

use crate::ts::operations::Product;
use crate::ts::{DefaultIdType, PredecessorIterable, StateIndex, SymbolOf, WordTs};
use crate::{Pointed, TransitionSystem, NTS};
use automata_core::alphabet::{Alphabet, CharAlphabet, SimpleAlphabet};
use automata_core::word::OmegaWord;
use automata_core::Color;
use automata_core::Void;

/// A nondeterministic Büchi automaton (NBA) is a nondeterministic transition system with Büchi acceptance condition.
#[derive(Debug, Clone)]
pub struct NBA<A: Alphabet = CharAlphabet, C: Color = Void> {
    ts: NTS<A, bool, C>,
    initial: Vec<DefaultIdType>,
}

impl<A: Alphabet, C: Color> NBA<A, C> {
    /// Creates a new instance from the given transition system, initial state and
    /// acceptance condition.
    pub fn from_parts(
        ts: NTS<A, bool, C>,
        initial_states: impl IntoIterator<Item = DefaultIdType>,
    ) -> NBA<A, C> {
        NBA {
            ts,
            initial: initial_states.into_iter().collect(),
        }
    }
    /// Decomposes the NBA into its parts: the transition system and the initial state.
    pub fn into_parts(self) -> (NTS<A, bool, C>, Vec<DefaultIdType>) {
        (self.ts, self.initial)
    }
    /// Returns a reference to the vector of initial states.
    pub fn initial_states(&self) -> &[DefaultIdType] {
        debug_assert_eq!(
            self.initial.len(),
            std::collections::BTreeSet::from_iter(self.initial.iter().cloned()).len()
        );
        &self.initial
    }
    /// Returns an iterator over the initial states.
    pub fn initial_states_iter(&self) -> impl Iterator<Item = DefaultIdType> + '_ {
        self.initial.iter().cloned()
    }

    /// Returns `true` if the given word is accepted by the automaton, `false` otherwise.
    pub fn accepts<W: OmegaWord<Symbol = SymbolOf<Self>>>(&self, input: W) -> bool
    where
        A: SimpleAlphabet,
    {
        self.initial.iter().any(|&i| self.accepts_from(&input, i))
    }

    /// Returns `true` if the given word is accepted by the automaton starting from the given state.
    pub fn accepts_from<W: OmegaWord<Symbol = SymbolOf<Self>>>(
        &self,
        input: W,
        from: StateIndex<Self>,
    ) -> bool
    where
        A: SimpleAlphabet,
    {
        let word_ts: WordTs<'_, A, W, true> = WordTs::new(self.alphabet(), input);
        let prod = self.ts.borrow().with_initial(from).ts_product(&word_ts);

        let sccs = prod.reachable_sccs_from(prod.reachable_state_indices());
        for (_i, scc) in sccs.iter() {
            if !scc.is_terminal() || scc.is_transient() {
                continue;
            }
            for q in scc.iter() {
                if prod.state_color(*q).map_or(false, |b| b.0) {
                    return true;
                }
            }
        }
        false
    }
}

impl<A: Alphabet, C: Color> TransitionSystem for NBA<A, C> {
    type Alphabet = A;
    type StateColor = bool;
    type EdgeColor = C;
    type EdgeRef<'this> = <NTS<A, bool, C> as TransitionSystem>::EdgeRef<'this> where Self: 'this;
    type EdgesFromIter<'this> = <NTS<A, bool, C> as TransitionSystem>::EdgesFromIter<'this> where Self: 'this;
    type StateIndex = DefaultIdType;
    type StateIndices<'this> = <NTS<A, bool, C> as TransitionSystem>::StateIndices<'this>
    where
        Self: 'this;
    fn edges_from(&self, state: crate::ts::StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        self.ts.edges_from(state)
    }
    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }
    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.ts.state_indices()
    }
    fn state_color(&self, state: crate::ts::StateIndex<Self>) -> Option<Self::StateColor> {
        self.ts.state_color(state)
    }
}
impl<A: Alphabet, C: Color> PredecessorIterable for NBA<A, C> {
    type PreEdgeRef<'this> = <NTS<A, bool, C> as PredecessorIterable>::PreEdgeRef<'this> where Self: 'this;
    type EdgesToIter<'this> = <NTS<A, bool, C> as PredecessorIterable>::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors(&self, state: crate::ts::StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        self.ts.predecessors(state)
    }
}
impl<A: Alphabet, C: Color> Pointed for NBA<A, C> {
    fn initial(&self) -> crate::ts::StateIndex<Self> {
        assert_eq!(
            self.initial.len(),
            1,
            "calling initial() on NBA is only allowed if it has precisely one initial state"
        );
        self.initial[0]
    }
}

#[cfg(test)]
mod tests {
    use automata_core::upw;

    use crate::ts::TSBuilder;

    #[test]
    fn nba_acceptance() {
        let nba = TSBuilder::without_edge_colors()
            .with_state_colors([false, true])
            .with_edges([
                (0, 'a', 0),
                (0, 'b', 0),
                (0, 'a', 1),
                (0, 'b', 1),
                (1, 'a', 1),
            ])
            .into_nba([0]);

        for pos in [upw!("a"), upw!("bababbbabb", "a")] {
            assert!(nba.accepts(pos))
        }
        for neg in [upw!("ab"), upw!("b"), upw!("abba", "b")] {
            if nba.accepts(&neg) {
                panic!("expected {:?} to be rejected", neg);
            }
        }
    }
}
