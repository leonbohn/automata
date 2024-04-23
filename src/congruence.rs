use std::{fmt::Debug, hash::Hash};

use crate::prelude::*;
use itertools::Itertools;

mod class;
pub use class::Class;

mod forc;
pub use forc::FORC;

mod transitionprofile;
pub use transitionprofile::{
    Accumulates, ReducingMonoid, ReplacingMonoid, RunProfile, RunSignature, TransitionMonoid,
};

mod cayley;
pub use cayley::{Cayley, RightCayley};

/// Represents a right congruence relation, which is in essence a trim, deterministic
/// transition system with a designated initial state.
#[derive(Clone)]
pub struct RightCongruence<A: Alphabet = CharAlphabet, Q = Void, C = Void> {
    ts: DTS<A, Q, C>,
    initial: usize,
    minimal_representatives: Vec<Class<A::Symbol>>,
}

impl<A: Alphabet, Q: Clone, C: Clone> RightCongruence<A, Q, C> {
    /// Returns true if and only if
    pub fn congruent<W, V>(&self, word: W, other: V) -> bool
    where
        W: FiniteWord<A::Symbol>,
        V: FiniteWord<A::Symbol>,
    {
        self.reached_state_index(word).unwrap() == self.reached_state_index(other).unwrap()
    }

    /// Verifies whether an element of `self` is  idempotent, i.e. if the mr of the indexed
    /// class is u, then it should be that uu ~ u.
    pub fn is_idempotent<I: Indexes<Self>>(&self, elem: I) -> bool {
        let Some(idx) = elem.to_index(self) else {
            panic!("is_idempotent called for non-existent index");
        };
        let Some(mr) = self.class_name(idx) else {
            panic!("The class {} is not labeled!", idx);
        };
        if let Some(q) = self.get(elem) {
            self.reached_state_index_from(mr, q) == Some(q)
        } else {
            false
        }
    }

    /// Returns the [`Class`] that is referenced by `index`.
    #[inline(always)]
    pub fn class_name<Idx: Indexes<Self>>(&self, index: Idx) -> Option<&Class<A::Symbol>> {
        let idx = index.to_index(self)?;
        self.minimal_representatives.get(idx)
    }

    #[inline(always)]
    /// Returns the index of the class containing the given word.
    pub fn class_to_index(&self, class: &Class<A::Symbol>) -> Option<usize> {
        self.minimal_representatives
            .iter()
            .enumerate()
            .find_map(|(idx, c)| if c == class { Some(idx) } else { None })
    }

    /// Computes a DFA that accepts precisely those finite words which loop on the given `class`. Formally,
    /// if `u` represents the given class, then the DFA accepts precisely those words `w` such that `uw`
    /// is congruent to `u`.
    pub fn looping_words(&self, _class: &Class<A::Symbol>) -> DFA<A> {
        todo!()
    }

    /// Returns an iterator which yields pairs `(c, idx)` consisting of a reference `c` to the class name together
    /// with the corresponding index of the class.
    pub fn classes(&self) -> impl Iterator<Item = (&Class<A::Symbol>, usize)> + '_ {
        self.minimal_representatives
            .iter()
            .enumerate()
            .map(|(idx, c)| (c, idx))
    }

    /// Builds a [`RightCongruence`] from the given transition system. This first collects into a [`DTS`], obtains
    /// the correct initial state and then builds the list of minimal representatives.
    pub fn from_ts<Ts: Congruence<Alphabet = A, EdgeColor = C, StateColor = Q>>(ts: Ts) -> Self {
        let (ts, initial) = ts.collect_dts_pointed();
        let minimal_representatives = ts
            .minimal_representatives_from(initial)
            .sorted_by(|x, y| x.1.cmp(&y.1))
            .map(|(x, _)| x.into())
            .collect();
        Self {
            ts,
            initial,
            minimal_representatives,
        }
    }
}

impl<A: Alphabet, Q: Clone, C: Clone> Deterministic for RightCongruence<A, Q, C> {}

impl<A: Alphabet, Q: Clone, C: Clone> TransitionSystem for RightCongruence<A, Q, C> {
    type StateIndex = usize;
    type EdgeColor = C;
    type StateColor = Q;
    type EdgeRef<'this> = &'this crate::transition_system::impls::NTEdge<A::Expression, C> where Self: 'this;
    type EdgesFromIter<'this> = crate::transition_system::impls::NTSEdgesFromIter<'this, A::Expression, C>
    where
        Self: 'this;
    type StateIndices<'this> = std::ops::Range<usize> where Self: 'this;

    type Alphabet = A;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.ts.state_indices()
    }

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        let state = state.to_index(self)?;
        self.ts.edges_from(state)
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        let state = state.to_index(self)?;
        self.ts.state_color(state)
    }
}

impl<A: Alphabet, Q: Clone, C: Clone> Pointed for RightCongruence<A, Q, C> {
    fn initial(&self) -> Self::StateIndex {
        self.initial
    }
}

impl<A: Alphabet, Q: Clone, C: Clone> PredecessorIterable for RightCongruence<A, Q, C> {
    type PreEdgeRef<'this> = &'this crate::transition_system::impls::NTEdge<A::Expression, C>
where
    Self: 'this;

    type EdgesToIter<'this> = crate::transition_system::impls::NTSEdgesToIter<'this, A::Expression, C>
where
    Self: 'this;

    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        let state = state.to_index(self)?;
        self.ts.predecessors(state)
    }
}

impl<A: Alphabet + PartialEq, Q: Hash + Eq, C: Hash + Eq> PartialEq for RightCongruence<A, Q, C> {
    fn eq(&self, other: &Self) -> bool {
        self.initial == other.initial && self.ts.eq(&other.ts)
    }
}

impl<A: Alphabet + PartialEq, Q: Hash + Eq, C: Hash + Eq> Eq for RightCongruence<A, Q, C> {}

impl<A: Alphabet, Q: Clone + Debug, C: Clone + Debug> Debug for RightCongruence<A, Q, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.ts.build_transition_table(
                |q, c| format!("{}|{:?}", q.show(), c),
                |edge| edge.target().show()
            )
        )
    }
}
