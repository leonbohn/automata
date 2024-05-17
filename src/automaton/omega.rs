use crate::{hoa::HoaAlphabet, prelude::*, Set};

mod buchi;
pub use buchi::*;

mod parity;
pub use parity::*;

mod rabin;
pub use rabin::*;

mod muller;
pub use muller::*;

#[allow(missing_docs)]
mod acceptance_mask;
pub use acceptance_mask::AcceptanceMask;

/// Disambiguates between the different types of acceptance conditions. This is only
/// used in conjunction with [`OmegaAutomaton`]/[`DeterministicOmegaAutomaton`] when
/// the exact type is not known beforehand (such as when parsing an automaton). Usually
/// one should prefer using specific automaton types such as [`DBA`]/[`DPA`] etc.
#[derive(Debug, Clone, Eq, Copy, PartialEq, Ord, PartialOrd)]
#[allow(missing_docs)]
pub enum OmegaAcceptanceCondition {
    Parity(usize, usize),
    Buchi,
    Rabin,
    Streett,
    MaxParity,
    CoBuchi,
    Reachability,
    Safety,
}

impl OmegaAcceptanceCondition {
    /// Returns true if and only if the condition is satisfied by the given set of
    /// [`AcceptanceMask`]s.
    pub fn satisfied(&self, infset: &Set<AcceptanceMask>) -> bool {
        match self {
            OmegaAcceptanceCondition::Parity(_low, _high) => infset
                .iter()
                .map(|x| x.as_priority())
                .min()
                .map(|x| x % 2 == 0)
                .unwrap_or(false),
            _ => unimplemented!(),
        }
    }
}

/// Represents a generic omega automaton, i.e. an automaton over infinite words.
/// This type is mainly used when the exact type of automaton is not known beforehand
/// such as when parsing automata. One should prefer using specific types such as
/// [`DPA`] whenever possible.
pub struct OmegaAutomaton<A: Alphabet> {
    pub(super) ts: NTS<A, usize, AcceptanceMask>,
    pub(super) initial: usize,
    pub(super) acc: OmegaAcceptanceCondition,
}

/// A deterministic variant of [`OmegaAutomaton`].
pub struct DeterministicOmegaAutomaton<A: Alphabet> {
    pub(super) ts: DTS<A, usize, AcceptanceMask>,
    pub(super) initial: usize,
    pub(super) acc: OmegaAcceptanceCondition,
}

impl<A: Alphabet> OmegaAutomaton<A> {
    /// Creates a new instance from the given transition system, initial state and
    /// acceptance condition.
    pub fn new(
        ts: NTS<A, usize, AcceptanceMask>,
        initial: usize,
        acc: OmegaAcceptanceCondition,
    ) -> Self {
        Self { ts, initial, acc }
    }

    /// Attempts to convert `self` into a [`DeterministicOmegaAutomaton`]. Returns
    /// `None` if this is not possible because the transition system underlying `self`
    /// is not deterministic.
    pub fn into_deterministic(self) -> Option<DeterministicOmegaAutomaton<A>> {
        self.try_into().ok()
    }
}

impl<A: Alphabet> DeterministicOmegaAutomaton<A> {
    /// Creates a new instance from the given *deterministic* transition system,
    /// initial state and acceptance condition.
    pub fn new(
        ts: DTS<A, usize, AcceptanceMask>,
        initial: usize,
        acc: OmegaAcceptanceCondition,
    ) -> Self {
        Self { ts, initial, acc }
    }

    /// Consumes and converts `self` into a [`DPA`]. Since [`DPA`]s can capture the
    /// full class of omega-regular languages, this operation never fails.
    pub fn into_dpa(self) -> DPA<A> {
        assert!(
            matches!(self.acc, OmegaAcceptanceCondition::Parity(_, _)),
            "Can only turn DPA into DPA for now"
        );

        self.ts
            .map_edge_colors(|mask| mask.as_priority())
            .with_initial(self.initial)
            .collect_dpa()
    }
}

impl From<DeterministicOmegaAutomaton<HoaAlphabet>> for DeterministicOmegaAutomaton<CharAlphabet> {
    fn from(value: DeterministicOmegaAutomaton<HoaAlphabet>) -> Self {
        let size = value.size();
        let ts = TSBuilder::default()
            .with_state_colors((0..size).map(|i| value.state_color(i).unwrap()))
            .with_transitions(value.state_indices().flat_map(|q| {
                assert!(q < size);
                value.edges_from(q).unwrap().flat_map(|edge| {
                    edge.expression()
                        .chars_iter()
                        .map(move |sym| (edge.source(), sym, edge.color(), edge.target()))
                })
            }))
            .into_dts();
        DeterministicOmegaAutomaton::new(ts, value.initial, value.acc)
    }
}

impl TryFrom<DeterministicOmegaAutomaton<CharAlphabet>>
    for DeterministicOmegaAutomaton<HoaAlphabet>
{
    /// For now, we allow this to error out in exactly one case: if the number of alphabet symbols
    /// is not a power of 2 and cannot be mapped immediately into AP combinations.
    type Error = String;
    fn try_from(value: DeterministicOmegaAutomaton<CharAlphabet>) -> Result<Self, Self::Error> {
        let size = value.size();
        let mut ts = DTS::for_alphabet(HoaAlphabet::try_from_char_alphabet(value.alphabet())?);

        for q in value.state_indices() {
            assert!(q < size, "The state indices must be contiguous for this!");
            ts.add_state(value.state_color(q).unwrap());
        }

        for q in value.state_indices() {
            for edge in value.edges_from(q).unwrap() {
                ts.add_edge((
                    edge.source(),
                    ts.alphabet()
                        .make_expression(ts.alphabet().char_to_hoa_symbol(*edge.expression())),
                    edge.color(),
                    edge.target(),
                ))
            }
        }

        assert!(value.initial() < size);
        Ok(DeterministicOmegaAutomaton::new(
            ts,
            value.initial,
            value.acc,
        ))
    }
}

impl<A: Alphabet> TryFrom<OmegaAutomaton<A>> for DeterministicOmegaAutomaton<A> {
    /// The only way this can go wrong is if the given automaton is not deterministic.
    type Error = ();

    fn try_from(value: OmegaAutomaton<A>) -> Result<Self, Self::Error> {
        let dts = value.ts.try_into()?;
        Ok(Self::new(dts, value.initial, value.acc))
    }
}

impl<A: Alphabet> TryFrom<&OmegaAutomaton<A>> for DeterministicOmegaAutomaton<A> {
    /// The only way this can go wrong is if the given automaton is not deterministic.
    type Error = ();

    fn try_from(value: &OmegaAutomaton<A>) -> Result<Self, Self::Error> {
        let dts = (&value.ts).try_into()?;
        Ok(Self::new(dts, value.initial, value.acc))
    }
}

impl<A: Alphabet> Pointed for OmegaAutomaton<A> {
    fn initial(&self) -> Self::StateIndex {
        self.initial
    }
}

impl<A: Alphabet> Pointed for DeterministicOmegaAutomaton<A> {
    fn initial(&self) -> Self::StateIndex {
        self.initial
    }
}

impl<A: Alphabet> TransitionSystem for OmegaAutomaton<A> {
    type StateIndex = usize;

    type StateColor = usize;

    type EdgeColor = AcceptanceMask;

    type EdgeRef<'this> = <DTS<A, usize, AcceptanceMask> as TransitionSystem>::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this> = <DTS<A, usize, AcceptanceMask> as TransitionSystem>::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this> = <DTS<A, usize, AcceptanceMask> as TransitionSystem>::StateIndices<'this>
    where
        Self: 'this;

    type Alphabet = A;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.ts.state_indices()
    }

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        self.ts.edges_from(state.to_index(self)?)
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        self.ts.state_color(state.to_index(self)?)
    }
}

impl<A: Alphabet> TransitionSystem for DeterministicOmegaAutomaton<A> {
    type StateIndex = usize;

    type StateColor = usize;

    type EdgeColor = AcceptanceMask;

    type EdgeRef<'this> = <DTS<A, usize, AcceptanceMask> as TransitionSystem>::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this> = <DTS<A, usize, AcceptanceMask> as TransitionSystem>::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this> = <DTS<A, usize, AcceptanceMask> as TransitionSystem>::StateIndices<'this>
    where
        Self: 'this;

    type Alphabet = A;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.ts.state_indices()
    }

    fn edges_from<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesFromIter<'_>> {
        self.ts.edges_from(state.to_index(self)?)
    }

    fn state_color<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::StateColor> {
        self.ts.state_color(state.to_index(self)?)
    }
}

impl<A: Alphabet> PredecessorIterable for OmegaAutomaton<A> {
    type PreEdgeRef<'this> = <DTS<A, usize, AcceptanceMask> as PredecessorIterable>::PreEdgeRef<'this>
    where
        Self: 'this;

    type EdgesToIter<'this> =  <DTS<A, usize, AcceptanceMask> as PredecessorIterable>::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        self.ts.predecessors(state.to_index(self)?)
    }
}

impl<A: Alphabet> PredecessorIterable for DeterministicOmegaAutomaton<A> {
    type PreEdgeRef<'this> = <DTS<A, usize, AcceptanceMask> as PredecessorIterable>::PreEdgeRef<'this>
    where
        Self: 'this;

    type EdgesToIter<'this> =  <DTS<A, usize, AcceptanceMask> as PredecessorIterable>::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors<Idx: Indexes<Self>>(&self, state: Idx) -> Option<Self::EdgesToIter<'_>> {
        self.ts.predecessors(state.to_index(self)?)
    }
}

impl<A: Alphabet> Deterministic for DeterministicOmegaAutomaton<A> {
    fn transition<Idx: Indexes<Self>>(
        &self,
        state: Idx,
        symbol: SymbolOf<Self>,
    ) -> Option<Self::EdgeRef<'_>> {
        self.ts.transition(state.to_index(self)?, symbol)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn omega_acceptance_conditions() {}
}
