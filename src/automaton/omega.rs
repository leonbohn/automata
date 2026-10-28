mod buchi;

pub use buchi::*;

mod parity;
pub use parity::*;

mod rabin;
pub use rabin::*;

mod muller;
pub use muller::*;

mod acceptance_mask;
use super::InfiniteWordAutomaton;
use crate::Error;
use crate::Int;
use crate::alphabet::{Alphabet, CharAlphabet, PropAlphabet, PropAlphabetError};
use crate::representation::IntoTs;
use crate::ts::{Builder, DefaultIdType, DenseId, ForAlphabet, IsEdge, Sproutable};
use crate::{DTS, Pointed, TS, TransitionSystem};
pub use acceptance_mask::{AcceptanceError, AcceptanceMask};
use std::collections::BTreeSet;

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
pub enum OmegaAcceptanceCondition {
    /// Parity condition on the priorities `low..=high` (usually `0..=n`): the smallest priority
    /// that is seen infinitely often has to be even.
    Parity(Int, Int),
    /// Büchi condition: the edges in acceptance set `0` are seen infinitely often.
    Buchi,
    /// Rabin condition (not supported by most operations yet).
    Rabin,
    /// Streett condition (not supported by most operations yet).
    Streett,
    /// Parity condition on the priorities `low..=high` where the *largest* priority that is seen
    /// infinitely often decides: a run is accepting if `high` minus that priority is even.
    MaxParity(Int, Int),
    /// Co-Büchi condition: the edges in acceptance set `0` are seen only finitely often.
    CoBuchi,
    /// Reachability condition: the edges in acceptance set `0` are the goal edges. Like
    /// [`OmegaAcceptanceCondition::Buchi`] it only looks at the edges seen infinitely often, so
    /// it is meant for automata in which goal edges lead into an accepting sink.
    Reachability,
    /// Safety condition: the edges in acceptance set `0` are the violating edges. Like
    /// [`OmegaAcceptanceCondition::CoBuchi`] it only looks at the edges seen infinitely often, so
    /// it is meant for automata in which violating edges lead into a rejecting sink.
    Safety,
}

impl OmegaAcceptanceCondition {
    /// Returns true if and only if the condition is satisfied by the given set of
    /// [`AcceptanceMask`]s, which are the masks of the edges seen infinitely often by a run.
    ///
    /// [`OmegaAcceptanceCondition::Reachability`] and [`OmegaAcceptanceCondition::Safety`] are
    /// evaluated like [`OmegaAcceptanceCondition::Buchi`] and
    /// [`OmegaAcceptanceCondition::CoBuchi`], respectively, which matches the behaviour of
    /// [`DeterministicOmegaAutomaton::into_dpa`].
    ///
    /// # Errors
    /// For the parity conditions every mask needs exactly one acceptance set within the range
    /// of the condition, otherwise an [`Error::Acceptance`] is returned.
    /// [`OmegaAcceptanceCondition::Rabin`] and [`OmegaAcceptanceCondition::Streett`] yield
    /// [`Error::NotYetImplemented`].
    pub fn satisfied(&self, infset: &BTreeSet<AcceptanceMask>) -> Result<bool, Error> {
        match self {
            OmegaAcceptanceCondition::Parity(low, high) => {
                let min = Self::priorities(infset, *low, *high)?.into_iter().min();
                Ok(min.is_some_and(|x| x % 2 == 0))
            }
            OmegaAcceptanceCondition::MaxParity(low, high) => {
                let max = Self::priorities(infset, *low, *high)?.into_iter().max();
                Ok(max.is_some_and(|x| (high - x) % 2 == 0))
            }
            OmegaAcceptanceCondition::Buchi | OmegaAcceptanceCondition::Reachability => {
                Ok(infset.iter().any(AcceptanceMask::as_bool))
            }
            OmegaAcceptanceCondition::CoBuchi | OmegaAcceptanceCondition::Safety => {
                Ok(!infset.iter().any(AcceptanceMask::as_bool))
            }
            OmegaAcceptanceCondition::Rabin | OmegaAcceptanceCondition::Streett => Err(
                Error::NotYetImplemented("checking satisfaction for Rabin and Streett conditions"),
            ),
        }
    }

    fn priorities(
        infset: &BTreeSet<AcceptanceMask>,
        low: Int,
        high: Int,
    ) -> Result<Vec<Int>, AcceptanceError> {
        infset
            .iter()
            .map(|mask| {
                let priority = mask.try_as_priority()?;
                if priority < low || priority > high {
                    return Err(AcceptanceError::PriorityOutOfRange {
                        priority,
                        low,
                        high,
                    });
                }
                Ok(priority)
            })
            .collect()
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
    /// [`OmegaAcceptanceCondition::Reachability`] and [`OmegaAcceptanceCondition::Safety`] are
    /// converted like [`OmegaAcceptanceCondition::Buchi`] and
    /// [`OmegaAcceptanceCondition::CoBuchi`], respectively.
    ///
    /// The conversion is not implemented for [`OmegaAcceptanceCondition::Rabin`] and
    /// [`OmegaAcceptanceCondition::Streett`]; these yield [`Error::NotYetImplemented`].
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
            OmegaAcceptanceCondition::Buchi | OmegaAcceptanceCondition::Reachability => Ok(self
                .ts
                .map_edge_colors(|mask| if mask.as_bool() { 0 } else { 1 })
                .with_initial(self.initial)
                .into_dpa()),
            OmegaAcceptanceCondition::CoBuchi | OmegaAcceptanceCondition::Safety => Ok(self
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
        }
    }
}

impl From<DeterministicOmegaAutomaton<PropAlphabet>> for DeterministicOmegaAutomaton<CharAlphabet> {
    fn from(value: DeterministicOmegaAutomaton<PropAlphabet>) -> Self {
        let size = value.size().into_id();
        let ts = Builder::default()
            .with_state_colors((0..size).map(|i| value.state_color(i).unwrap().into_owned()))
            .with_transitions(value.state_indices().flat_map(|q| {
                assert!(q < size);
                value.edges_from(q).unwrap().flat_map(|edge| {
                    edge.expression().chars_iter().map(move |sym| {
                        (
                            edge.source(),
                            sym,
                            IsEdge::color(&edge).into_owned(),
                            edge.target(),
                        )
                    })
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
            ts.add_state(value.state_color(q).unwrap().into_owned());
        }

        for q in value.state_indices() {
            for edge in value.edges_from(q).unwrap() {
                ts.add_edge((
                    edge.source(),
                    ts.alphabet()
                        .make_expression(ts.alphabet().char_to_symbol(*edge.expression())),
                    edge.color().into_owned(),
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

    fn infset(masks: &[&[Int]]) -> BTreeSet<AcceptanceMask> {
        masks
            .iter()
            .map(|m| AcceptanceMask::from_iter(m.iter().copied()))
            .collect()
    }

    #[test]
    fn satisfied_parity() {
        use OmegaAcceptanceCondition::{MaxParity, Parity};
        assert_eq!(Parity(0, 2).satisfied(&infset(&[])), Ok(false));
        assert_eq!(Parity(0, 2).satisfied(&infset(&[&[0], &[1]])), Ok(true));
        assert_eq!(Parity(0, 2).satisfied(&infset(&[&[1], &[2]])), Ok(false));
        assert_eq!(MaxParity(0, 2).satisfied(&infset(&[&[2], &[1]])), Ok(true));
        assert_eq!(MaxParity(0, 2).satisfied(&infset(&[&[0], &[1]])), Ok(false));
        assert_eq!(MaxParity(0, 2).satisfied(&infset(&[])), Ok(false));
        assert_eq!(
            Parity(0, 2).satisfied(&infset(&[&[3]])),
            Err(Error::Acceptance(AcceptanceError::PriorityOutOfRange {
                priority: 3,
                low: 0,
                high: 2
            }))
        );
        assert_eq!(
            MaxParity(0, 2).satisfied(&infset(&[&[]])),
            Err(Error::Acceptance(AcceptanceError::NoAcceptanceSet))
        );
    }

    #[test]
    fn satisfied_buchi_like() {
        use OmegaAcceptanceCondition::{Buchi, CoBuchi, Reachability, Safety};
        for good in [Buchi, Reachability] {
            assert_eq!(good.satisfied(&infset(&[])), Ok(false));
            assert_eq!(good.satisfied(&infset(&[&[]])), Ok(false));
            assert_eq!(good.satisfied(&infset(&[&[], &[0]])), Ok(true));
        }
        for bad in [CoBuchi, Safety] {
            assert_eq!(bad.satisfied(&infset(&[])), Ok(true));
            assert_eq!(bad.satisfied(&infset(&[&[]])), Ok(true));
            assert_eq!(bad.satisfied(&infset(&[&[], &[0]])), Ok(false));
        }
    }

    #[test]
    fn satisfied_reports_unsupported_conditions() {
        for unsupported in [
            OmegaAcceptanceCondition::Rabin,
            OmegaAcceptanceCondition::Streett,
        ] {
            assert!(matches!(
                unsupported.satisfied(&infset(&[])),
                Err(Error::NotYetImplemented(_))
            ));
        }
    }

    /// `into_dpa` and `satisfied` have to agree on a one-state automaton that loops on `mask`.
    #[test]
    fn into_dpa_agrees_with_satisfied() {
        use OmegaAcceptanceCondition::*;
        let cases = [
            (Parity(0, 2), vec![0], true),
            (Parity(0, 2), vec![1], false),
            (MaxParity(0, 2), vec![2], true),
            (MaxParity(0, 2), vec![1], false),
            (Buchi, vec![0], true),
            (Buchi, vec![], false),
            (CoBuchi, vec![0], false),
            (CoBuchi, vec![], true),
            (Reachability, vec![0], true),
            (Reachability, vec![], false),
            (Safety, vec![0], false),
            (Safety, vec![], true),
        ];
        for (acc, mask, expected) in cases {
            let mask = AcceptanceMask::from_iter(mask);
            let set: BTreeSet<_> = [mask.clone()].into_iter().collect();
            assert_eq!(acc.satisfied(&set), Ok(expected), "{acc:?} {mask:?}");

            let dpa = two_state_automaton(acc, mask).into_dpa().unwrap();
            let word = crate::upw!("a");
            assert_eq!(dpa.accepts(&word), expected, "{acc:?}");
        }
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
            OmegaAcceptanceCondition::Reachability,
            OmegaAcceptanceCondition::Safety,
        ] {
            assert!(single_state_automaton(supported).into_dpa().is_ok());
        }
    }
}
