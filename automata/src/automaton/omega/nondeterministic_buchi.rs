use std::borrow::Borrow;
use std::collections::BTreeSet;

use crate::dot::{DotTransitionAttribute, Dottable};
use crate::ts::operations::Product;
use crate::ts::{
    DefaultIdType, ForAlphabet, PredecessorIterable, Shrinkable, Sproutable, StateIndex, SymbolOf,
    WordTs,
};
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
    /// Removes all states that are not reachable from the initial states.
    /// Returns a vector of the removed state indices.
    pub fn trim(&mut self) -> Vec<DefaultIdType> {
        let mut reachable = BTreeSet::new();
        for initial in &self.initial {
            reachable.extend(self.ts.reachable_state_indices_from(*initial));
        }
        let mut removed = vec![];
        for state_index in self.ts.state_indices_vec() {
            if !reachable.contains(&state_index) {
                self.ts.remove_state(state_index);

                debug_assert!(!removed.contains(&state_index));
                removed.push(state_index);
            }
        }
        for state_index in self.ts.state_indices_vec() {
            let reached = self
                .ts
                .reachable_state_indices_from(state_index)
                .collect::<Vec<_>>();
            if !reached.iter().any(|q| self.ts.state_color(*q).unwrap()) {
                self.ts.remove_state(state_index);
                removed.push(state_index);
            }
        }
        removed
    }
    /// Creates a new NBA for the given alphabet, containing states with the given colors.
    pub fn from_state_colors(alphabet: A, iter: impl IntoIterator<Item = bool>) -> NBA<A, C> {
        use crate::ts::Sproutable;

        let mut nts = NTS::for_alphabet(alphabet);
        for state_color in iter.into_iter() {
            nts.add_state(state_color);
        }

        NBA {
            ts: nts,
            initial: vec![],
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
    /// Adds the given state to the set of initial states. Returns `true` if the state was not already in the set.
    /// Returns `false` otherwise.
    pub fn add_initial_state(&mut self, state: DefaultIdType) -> bool {
        if self.initial.contains(&state) {
            false
        } else {
            self.initial.push(state);
            true
        }
    }
    /// Replaces the initial states with the given ones.
    pub fn with_initial_states(self, initials: impl IntoIterator<Item = DefaultIdType>) -> Self {
        NBA {
            initial: initials.into_iter().collect(),
            ..self
        }
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
impl<A: Alphabet, C: Color> Sproutable for NBA<A, C> {
    fn add_state(&mut self, color: crate::ts::StateColor<Self>) -> Self::StateIndex {
        self.ts.add_state(color)
    }

    fn add_edge<E>(&mut self, t: E) -> Option<crate::ts::EdgeTuple<Self>>
    where
        E: crate::ts::IntoEdgeTuple<Self>,
    {
        self.ts.add_edge(t.into_edge_tuple())
    }

    fn set_state_color(&mut self, index: StateIndex<Self>, color: crate::ts::StateColor<Self>) {
        self.ts.set_state_color(index, color);
    }
}
impl<A: Alphabet, C: Color> Dottable for NBA<A, C> {
    fn dot_name(&self) -> Option<String> {
        Some("NBA".into())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx}")
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = crate::dot::DotStateAttribute> {
        if self.ts.state_color(idx).unwrap() {
            vec![crate::dot::DotStateAttribute::Shape(
                crate::dot::DotShape::DoubleCircle,
            )]
        } else {
            vec![crate::dot::DotStateAttribute::Shape(
                crate::dot::DotShape::Circle,
            )]
        }
    }
    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = crate::dot::DotTransitionAttribute> {
        use crate::ts::IsEdge;
        [DotTransitionAttribute::Label(automata_core::Show::show(
            &t.expression(),
        ))]
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
        let mut copy = nba.clone();
        let removed = copy.trim();
        assert_eq!(removed, vec![]);

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
