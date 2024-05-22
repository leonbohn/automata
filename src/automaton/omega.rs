use crate::{hoa::HoaAlphabet, math::Set, prelude::*};

mod buchi;
pub use buchi::*;

mod parity;
pub use parity::*;

mod rabin;
use petgraph::graph::NodeIndex;
pub use rabin::*;

mod muller;
pub use muller::*;

#[allow(missing_docs)]
mod acceptance_mask;
pub use acceptance_mask::AcceptanceMask;
use tracing::{error, trace};

use super::InfiniteWordAutomaton;

/// Type alias for an omega automaton (i.e. an [`InfiniteWordAutomaton`]) that is guaranteed to be
/// [`Deterministic`].
pub type DeterministicOmegaAutomaton<A> = OmegaAutomaton<A, true>;
/// Type alias for an omega automaton (i.e. an [`InfiniteWordAutomaton`]) that is not necessarily
/// [`Deterministic`].
pub type NondeterministicOmegaAutomaton<A> = OmegaAutomaton<A, false>;

/// Represents a generic omega automaton, i.e. an automaton over infinite words.
/// This type is mainly used when the exact type of automaton is not known beforehand
/// such as when parsing automata. One should prefer using specific types such as
/// [`DPA`] whenever possible.
pub type OmegaAutomaton<A, const DET: bool = true> =
    InfiniteWordAutomaton<A, OmegaAcceptanceCondition, usize, AcceptanceMask, DET>;

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

impl<A: Alphabet, const DET: bool> OmegaAutomaton<A, DET> {
    /// Creates a new instance from the given transition system, initial state and
    /// acceptance condition.
    pub fn new(
        ts: TS<A, usize, AcceptanceMask, DET>,
        initial: NodeIndex,
        acceptance: OmegaAcceptanceCondition,
    ) -> OmegaAutomaton<A, DET> {
        OmegaAutomaton {
            ts,
            initial,
            acceptance,
        }
    }
    /// Attempts to convert `self` into a [`DeterministicOmegaAutomaton`]. Returns
    /// `None` if this is not possible because the transition system underlying `self`
    /// is not deterministic.
    pub fn into_deterministic(self) -> DeterministicOmegaAutomaton<A> {
        match self.try_into_deterministic() {
            Ok(dts) => {
                trace!("Converted into deterministic: {:?}", dts);
                dts
            }
            Err(nts) => {
                error!(
                    "Tried to convert non-deterministic omega automaton into deterministic: \n{:?}",
                    nts
                );
                panic!("Automaton that we want to convert is not deterministic!")
            }
        }
    }
    /// Attempts to convert `self` into a [`DeterministicOmegaAutomaton`]. Returns
    /// `None` if this is not possible because the transition system underlying `self`
    /// is not deterministic.
    pub fn try_into_deterministic(self) -> Result<DeterministicOmegaAutomaton<A>, Self> {
        let OmegaAutomaton {
            ts,
            initial,
            acceptance,
        } = self;
        match ts.try_into_deterministic() {
            Ok(dts) => Ok(DeterministicOmegaAutomaton::new(dts, initial, acceptance)),
            Err(ts) => Err(Self {
                ts,
                initial,
                acceptance,
            }),
        }
    }
}

impl<A: Alphabet> DeterministicOmegaAutomaton<A> {
    /// Consumes and converts `self` into a [`DPA`]. Since [`DPA`]s can capture the
    /// full class of omega-regular languages, this operation never fails.
    pub fn into_dpa(self) -> DPA<A> {
        assert!(
            matches!(self.acceptance, OmegaAcceptanceCondition::Parity(_, _)),
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
                assert!(q.index() < size);
                value.edges_from(q).unwrap().flat_map(|edge| {
                    edge.expression().chars_iter().map(move |sym| {
                        (
                            edge.source().index(),
                            sym,
                            edge.color(),
                            edge.target().index(),
                        )
                    })
                })
            }))
            .into_dts();
        DeterministicOmegaAutomaton::new(ts, value.initial, value.acceptance)
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
            assert!(
                q.index() < size,
                "The state indices must be contiguous for this!"
            );
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
                ));
            }
        }

        assert!(value.initial().index() < size);
        Ok(DeterministicOmegaAutomaton::new(
            ts,
            value.initial,
            value.acceptance,
        ))
    }
}
