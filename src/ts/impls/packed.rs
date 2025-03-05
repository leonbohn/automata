use crate::TransitionSystem;
use crate::core::{Color, alphabet::SimpleAlphabet};
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{Deterministic, IsEdge, StateIndex};

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Id(pub usize);

impl std::ops::Deref for Id {
    type Target = usize;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for Id {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub struct Packed<A: SimpleAlphabet, Q: Color, C: Color> {
    alphabet: A,
    states: Vec<Option<Q>>,
    edges: Vec<PackedEdge<A, C>>,
}

impl<A: SimpleAlphabet, Q: Color, C: Color> Packed<A, Q, C> {
    pub fn new(alphabet: A, states: Vec<Option<Q>>, edges: Vec<PackedEdge<A, C>>) -> Self {
        Self {
            alphabet,
            states,
            edges,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct PackedEdge<A: SimpleAlphabet, C: Color> {
    source: Id,
    target: Id,
    expression: A::Expression,
    color: C,
}

impl<A: SimpleAlphabet, C: Color> PackedEdge<A, C> {
    pub fn new(source: Id, expression: A::Expression, color: C, target: Id) -> Self {
        Self {
            source,
            target,
            expression,
            color,
        }
    }
}

impl<A: SimpleAlphabet, Q: Color, C: Color> TransitionSystem for Packed<A, Q, C> {
    type Alphabet = A;

    type StateIndex = Id;

    type StateColor = Q;

    type EdgeColor = C;

    type EdgeRef<'this>
        = &'this PackedEdge<A, C>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = std::slice::Iter<'this, PackedEdge<A, C>>
    where
        Self: 'this;

    type StateIndices<'this>
        = PackedStateIndices<'this, Q>
    where
        Self: 'this;

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        let Some(Some(_color)) = self.states.get(*state) else {
            return None;
        };
        let start = *state * self.alphabet.size();
        let end = start + self.alphabet.size();
        Some(self.edges[start..end].iter())
    }

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        PackedStateIndices::new(&self.states)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        let c = self.states.get(*state)?;
        c.clone()
    }
}

impl<A: SimpleAlphabet, Q: Color, C: Color> Deterministic for Packed<A, Q, C> {}

impl<A: SimpleAlphabet, Q: Color, C: Color> PredecessorIterable for Packed<A, Q, C> {
    type PreEdgeRef<'this>
        = &'this PackedEdge<A, C>
    where
        Self: 'this;

    type EdgesToIter<'this>
        =
        std::iter::Filter<std::slice::Iter<'this, PackedEdge<A, C>>, fn(&&PackedEdge<A, C>) -> bool>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        todo!()
    }
}

pub struct PackedEdgesFrom<'a, A: SimpleAlphabet, C: Color> {
    array: &'a [PackedEdge<A, C>],
    end: usize,
    pos: usize,
}

impl<'a, A: SimpleAlphabet, C: Color> Iterator for PackedEdgesFrom<'a, A, C> {
    type Item = &'a PackedEdge<A, C>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.end {
            assert!(self.end <= self.array.len());
            self.pos += 1;
            Some(&self.array[self.pos - 1])
        } else {
            None
        }
    }
}

impl<'a, A: SimpleAlphabet, C: Color> PackedEdgesFrom<'a, A, C> {
    pub fn new(array: &'a [PackedEdge<A, C>], pos: usize, end: usize) -> Self {
        if end > array.len() || pos > end {
            panic!(
                "invalid acces pos: {pos} end: {end} in length {} array\n{array:?}",
                array.len()
            );
        }
        Self { array, end, pos }
    }
}

pub struct PackedStateIndices<'a, Q> {
    array: &'a [Option<Q>],
    pos: usize,
    length: usize,
}

impl<Q> Iterator for PackedStateIndices<'_, Q> {
    type Item = Id;
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.length {
            self.pos += 1;
            Some(Id(self.pos - 1))
        } else {
            None
        }
    }
}

impl<'a, Q> PackedStateIndices<'a, Q> {
    pub fn new(array: &'a [Option<Q>]) -> Self {
        Self {
            array,
            pos: 0,
            length: array.len(),
        }
    }
}

impl<'a, A: SimpleAlphabet, C: Color> IsEdge<'a, A::Expression, Id, C> for &'a PackedEdge<A, C> {
    fn source(&self) -> Id {
        self.source
    }

    fn target(&self) -> Id {
        self.target
    }

    fn color(&self) -> C {
        self.color.clone()
    }

    fn expression(&self) -> &'a A::Expression {
        &self.expression
    }
}
