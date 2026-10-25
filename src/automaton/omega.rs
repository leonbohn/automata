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
use super::InfiniteWordAutomaton;
use crate::Error;
use crate::Int;
use crate::alphabet::{Alphabet, CharAlphabet, PropAlphabet, PropAlphabetError};
use crate::math::OrderedSet;
use crate::representation::IntoTs;
use crate::ts::{Builder, DefaultIdType, ForAlphabet, IsEdge, ScalarIndexType, Sproutable};
use crate::{DTS, Pointed, TS, TransitionSystem};
pub use acceptance_mask::{AcceptanceError, AcceptanceMask};

/// Type alias for an omega automaton (i.e. an [`InfiniteWordAutomaton`]) that is guaranteed to be
/// [`crate::Deterministic`].
pub type DeterministicOmegaAutomaton<A> = OmegaAutomaton<A, true>;
/// Type alias for an omega automaton (i.e. an [`InfiniteWordAutomaton`]) that is not necessarily
/// [`crate::Deterministic`].
pub type NondeterministicOmegaAutomaton<A> = OmegaAutomaton<A, false>;

/// Represents a generic omega automaton, i.e. an automaton over infinite words.
/// This type is mainly used when the exact type of automaton is not known beforehand
/// such as when parsing automata. One should prefer using specific types such as
/// [`DPA`] whenever possible.
pub type OmegaAutomaton<A, const DET: bool = true> =
    InfiniteWordAutomaton<A, OmegaAcceptanceCondition, Int, AcceptanceMask, DET>;

/// Disambiguates between the different types of acceptance conditions. This is only
/// used in conjunction with [`OmegaAutomaton`]/[`DeterministicOmegaAutomaton`] when
/// the exact type is not known beforehand (such as when parsing an automaton). Usually
/// one should prefer using specific automaton types such as [`DBA`]/[`DPA`] etc.
#[derive(Debug, Clone, Eq, Copy, PartialEq, Ord, PartialOrd)]
#[allow(missing_docs)]
pub enum OmegaAcceptanceCondition {
    Parity(Int, Int),
    Buchi,
    Rabin,
    Streett,
    MaxParity(Int, Int),
    CoBuchi,
    Reachability,
    Safety,
}

impl OmegaAcceptanceCondition {
    /// Returns true if and only if the condition is satisfied by the given set of
    /// [`AcceptanceMask`]s.
    ///
    /// # Errors
    /// Currently only [`OmegaAcceptanceCondition::Parity`] is supported, all other
    /// conditions yield [`Error::NotYetImplemented`].
    pub fn satisfied(&self, infset: &OrderedSet<AcceptanceMask>) -> Result<bool, Error> {
        match self {
            OmegaAcceptanceCondition::Parity(_low, _high) => Ok(infset
                .iter()
                .map(|x| x.as_priority())
                .min()
                .map(|x| x % 2 == 0)
                .unwrap_or(false)),
            _ => Err(Error::NotYetImplemented(
                "checking satisfaction for this acceptance condition",
            )),
        }
    }
}

impl<A: Alphabet, const DET: bool> OmegaAutomaton<A, DET> {
    /// Creates a new instance from the given transition system, initial state and
    /// acceptance condition.
    pub fn new(
        ts: TS<A, Int, AcceptanceMask, DET>,
        initial: DefaultIdType,
        acceptance: OmegaAcceptanceCondition,
    ) -> OmegaAutomaton<A, DET> {
        OmegaAutomaton {
            ts,
            initial,
            acceptance,
        }
    }
    /// Attempts to convert `self` into a [`DeterministicOmegaAutomaton`]. Returns
    /// `self` unchanged as the error if this is not possible because the transition system
    /// underlying `self` is not deterministic.
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
    /// Verifies that every edge has exactly one acceptance set and that the corresponding
    /// priority lies within `low..=high`.
    fn check_priorities(&self, low: Int, high: Int) -> Result<(), AcceptanceError> {
        for q in self.ts.state_indices() {
            for edge in self.ts.edges_from(q).into_iter().flatten() {
                let priority = edge.color().try_as_priority()?;
                if priority < low || priority > high {
                    return Err(AcceptanceError::PriorityOutOfRange {
                        priority,
                        low,
                        high,
                    });
                }
            }
        }
        Ok(())
    }

    /// Consumes and converts `self` into a [`DPA`]. Since [`DPA`]s can capture the
    /// full class of omega-regular languages, this is possible in principle for every
    /// acceptance condition.
    ///
    /// # Errors
    /// For parity conditions every edge needs exactly one acceptance set that lies within
    /// the range of the condition, otherwise an [`Error::Acceptance`] is returned.
    ///
    /// The conversion is not implemented for [`OmegaAcceptanceCondition::Rabin`],
    /// [`OmegaAcceptanceCondition::Streett`], [`OmegaAcceptanceCondition::Reachability`]
    /// and [`OmegaAcceptanceCondition::Safety`]; these yield [`Error::NotYetImplemented`].
    pub fn into_dpa(self) -> Result<DPA<A>, Error> {
        match self.acceptance {
            OmegaAcceptanceCondition::Parity(low, high) => self.check_priorities(low, high)?,
            OmegaAcceptanceCondition::MaxParity(low, high) => self.check_priorities(low, high)?,
            _ => {}
        }
        match self.acceptance {
            OmegaAcceptanceCondition::Parity(_, _) => Ok(self
                .ts
                .map_edge_colors(|mask| mask.as_priority())
                .with_initial(self.initial)
                .into_dpa()),
            OmegaAcceptanceCondition::Buchi => Ok(self
                .ts
                .map_edge_colors(|mask| if mask.as_bool() { 0 } else { 1 })
                .with_initial(self.initial)
                .into_dpa()),
            OmegaAcceptanceCondition::CoBuchi => Ok(self
                .ts
                .map_edge_colors(|mask| if mask.as_bool() { 1 } else { 0 })
                .with_initial(self.initial)
                .into_dpa()),
            OmegaAcceptanceCondition::MaxParity(low, high) => {
                let k = (high - low) + if low % 2 == 0 { 0 } else { 1 };
                let to_new = |mask: AcceptanceMask| {
                    // the priorities have been validated at the start of this function
                    let diff = high - mask.as_priority();
                    debug_assert!(diff <= k);
                    diff
                };
                Ok(self
                    .ts
                    .map_edge_colors(to_new)
                    .with_initial(self.initial)
                    .into_dpa())
            }
            OmegaAcceptanceCondition::Rabin => Err(Error::NotYetImplemented(
                "conversion of Rabin automata into DPA",
            )),
            OmegaAcceptanceCondition::Streett => Err(Error::NotYetImplemented(
                "conversion of Streett automata into DPA",
            )),
            OmegaAcceptanceCondition::Reachability => Err(Error::NotYetImplemented(
                "conversion of reachability automata into DPA",
            )),
            OmegaAcceptanceCondition::Safety => Err(Error::NotYetImplemented(
                "conversion of safety automata into DPA",
            )),
        }
    }
}

impl From<DeterministicOmegaAutomaton<PropAlphabet>> for DeterministicOmegaAutomaton<CharAlphabet> {
    fn from(value: DeterministicOmegaAutomaton<PropAlphabet>) -> Self {
        let size = value.size().into_index();
        let ts = Builder::default()
            .with_state_colors((0..size).map(|i| value.state_color(i).unwrap()))
            .with_transitions(value.state_indices().flat_map(|q| {
                assert!(q < size);
                value.edges_from(q).unwrap().flat_map(|edge| {
                    edge.expression()
                        .chars_iter()
                        .map(move |sym| (edge.source(), sym, IsEdge::color(&edge), edge.target()))
                })
            }))
            .into_dts();
        DeterministicOmegaAutomaton::new(ts, value.initial, value.acceptance)
    }
}

impl TryFrom<DeterministicOmegaAutomaton<CharAlphabet>>
    for DeterministicOmegaAutomaton<PropAlphabet>
{
    /// For now, we allow this to error out in exactly one case: if the number of alphabet symbols
    /// is not a power of 2 and cannot be mapped immediately into AP combinations.
    type Error = PropAlphabetError;
    fn try_from(value: DeterministicOmegaAutomaton<CharAlphabet>) -> Result<Self, Self::Error> {
        let size = value.size();
        let mut ts = DTS::for_alphabet(PropAlphabet::try_from_char_alphabet(value.alphabet())?);

        for q in value.state_indices() {
            assert!(
                q.into_usize() < size,
                "The state indices must be contiguous for this!"
            );
            ts.add_state(value.state_color(q).unwrap());
        }

        for q in value.state_indices() {
            for edge in value.edges_from(q).unwrap() {
                ts.add_edge((
                    edge.source(),
                    ts.alphabet()
                        .make_expression(ts.alphabet().char_to_symbol(*edge.expression())),
                    edge.color(),
                    edge.target(),
                ));
            }
        }

        assert!(value.initial().into_usize() < size);
        Ok(DeterministicOmegaAutomaton::new(
            ts,
            value.initial,
            value.acceptance,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Error;

    fn single_state_automaton(
        acceptance: OmegaAcceptanceCondition,
    ) -> DeterministicOmegaAutomaton<CharAlphabet> {
        let mut ts: DTS<CharAlphabet, Int, AcceptanceMask> =
            DTS::for_alphabet(CharAlphabet::of_size(1));
        let q = ts.add_state(0);
        DeterministicOmegaAutomaton::new(ts, q, acceptance)
    }

    #[test]
    fn satisfied_reports_unsupported_conditions() {
        let empty = OrderedSet::new();
        assert_eq!(
            OmegaAcceptanceCondition::Parity(0, 1).satisfied(&empty),
            Ok(false)
        );
        assert!(matches!(
            OmegaAcceptanceCondition::Buchi.satisfied(&empty),
            Err(Error::NotYetImplemented(_))
        ));
    }

    fn two_state_automaton(
        acceptance: OmegaAcceptanceCondition,
        mask: AcceptanceMask,
    ) -> DeterministicOmegaAutomaton<CharAlphabet> {
        let mut ts: DTS<CharAlphabet, Int, AcceptanceMask> =
            DTS::for_alphabet(CharAlphabet::of_size(1));
        let q = ts.add_state(0);
        ts.add_edge((q, 'a', mask, q));
        DeterministicOmegaAutomaton::new(ts, q, acceptance)
    }

    #[test]
    fn into_dpa_validates_priorities() {
        use crate::automaton::AcceptanceError;

        let parity = OmegaAcceptanceCondition::Parity(0, 2);
        assert!(
            two_state_automaton(parity, AcceptanceMask::from_iter([1]))
                .into_dpa()
                .is_ok()
        );
        assert_eq!(
            two_state_automaton(parity, AcceptanceMask::from_iter([]))
                .into_dpa()
                .err(),
            Some(Error::Acceptance(AcceptanceError::NoAcceptanceSet))
        );
        assert_eq!(
            two_state_automaton(parity, AcceptanceMask::from_iter([0, 1]))
                .into_dpa()
                .err(),
            Some(Error::Acceptance(AcceptanceError::MultipleAcceptanceSets(
                vec![0, 1]
            )))
        );
        assert_eq!(
            two_state_automaton(parity, AcceptanceMask::from_iter([5]))
                .into_dpa()
                .err(),
            Some(Error::Acceptance(AcceptanceError::PriorityOutOfRange {
                priority: 5,
                low: 0,
                high: 2
            }))
        );
        assert!(
            two_state_automaton(
                OmegaAcceptanceCondition::MaxParity(1, 3),
                AcceptanceMask::from_iter([2])
            )
            .into_dpa()
            .is_ok()
        );
    }

    #[test]
    fn into_dpa_reports_unsupported_conditions() {
        for unsupported in [
            OmegaAcceptanceCondition::Rabin,
            OmegaAcceptanceCondition::Streett,
            OmegaAcceptanceCondition::Reachability,
            OmegaAcceptanceCondition::Safety,
        ] {
            assert!(matches!(
                single_state_automaton(unsupported).into_dpa(),
                Err(Error::NotYetImplemented(_))
            ));
        }
        for supported in [
            OmegaAcceptanceCondition::Buchi,
            OmegaAcceptanceCondition::CoBuchi,
            OmegaAcceptanceCondition::Parity(0, 1),
        ] {
            assert!(single_state_automaton(supported).into_dpa().is_ok());
        }
    }
}
