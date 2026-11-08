mod buchi;

pub use buchi::*;

mod parity;
pub use parity::*;

mod rabin;
pub use rabin::*;

mod streett;
pub use streett::*;

mod muller;
pub use muller::*;
mod co_buchi;
pub use co_buchi::*;

mod acceptance_mask;
use super::Automaton;
use crate::Error;
use crate::Int;
use crate::Void;
use crate::alphabet::{Alphabet, CharAlphabet, PropAlphabet, PropAlphabetError};
use crate::automaton::semantics::observe_omega;
use crate::automaton::{CycleCondition, Existential, Semantics};
use crate::math;
use crate::representation::IntoTransitions;
use crate::ts::States;
use crate::ts::run;
use crate::ts::{Builder, DefaultIdType, ForAlphabet, Sproutable};
use crate::ts::{Det, Linked, Storage};
use crate::ts::{Deterministic, StateIndex, SymbolOf};
use crate::word::OmegaWord;
use crate::{DTS, NTS, Pointed, TransitionSystem};
pub use acceptance_mask::{AcceptanceError, AcceptanceMask};
use std::collections::BTreeMap;
use std::collections::BTreeSet;

/// Type alias for an omega automaton (i.e. an automaton over infinite words) that is guaranteed to be
/// [`crate::Deterministic`].
pub type DeterministicOmegaAutomaton<A> = OmegaAutomaton<A, Det<Linked>>;
/// Type alias for an omega automaton (i.e. an automaton over infinite words) that is not necessarily
/// [`crate::Deterministic`].
pub type NondeterministicOmegaAutomaton<A> = OmegaAutomaton<A, Linked>;

/// Represents a generic omega automaton, i.e. an automaton over infinite words.
/// This type is mainly used when the exact type of automaton is not known beforehand
/// such as when parsing automata. One should prefer using specific types such as
/// [`DPA`] whenever possible.
///
/// The storage `S` decides how the transition system is represented and whether it is
/// deterministic: [`Det<Linked>`] (the default) or [`Linked`].
///
/// The semantics are [`Storage::Semantics`] of the [`OmegaAcceptanceCondition`]: the condition
/// itself for deterministic storages and [`Existential`] for [`Linked`], so that both accept
/// words.
pub type OmegaAutomaton<A, S = Det<Linked>> = Automaton<
    <S as Storage<A>>::Ts<Int, AcceptanceMask>,
    <S as Storage<A>>::Semantics<OmegaAcceptanceCondition>,
>;

/// The four variants of a parity condition: whether the *minimum* or the *maximum* priority that
/// is seen infinitely often decides, and whether that priority has to be *even* or *odd* for a run
/// to be accepting. The typed counterparts are [`MinEvenParityCondition`],
/// [`MaxEvenParityCondition`], [`MinOddParityCondition`] and [`MaxOddParityCondition`]; in the HOA
/// format the kind is part of the `acc-name`, e.g. `parity max odd 3`.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ParityKind {
    /// The least priority seen infinitely often has to be even.
    MinEven,
    /// The greatest priority seen infinitely often has to be even.
    MaxEven,
    /// The least priority seen infinitely often has to be odd.
    MinOdd,
    /// The greatest priority seen infinitely often has to be odd.
    MaxOdd,
}

impl ParityKind {
    /// Returns true for the kinds in which the greatest priority decides, false if the least does.
    pub fn is_max(self) -> bool {
        matches!(self, Self::MaxEven | Self::MaxOdd)
    }

    /// Returns true for the kinds in which the deciding priority has to be even.
    pub fn is_even(self) -> bool {
        matches!(self, Self::MinEven | Self::MaxEven)
    }

    /// The priority that decides among the given ones, `None` if there are none.
    fn decisive(self, priorities: impl IntoIterator<Item = Int>) -> Option<Int> {
        let priorities = priorities.into_iter();
        if self.is_max() {
            priorities.max()
        } else {
            priorities.min()
        }
    }
}

/// Disambiguates between the different types of acceptance conditions. This is only
/// used in conjunction with [`OmegaAutomaton`]/[`DeterministicOmegaAutomaton`] when
/// the exact type is not known beforehand (such as when parsing an automaton). Usually
/// one should prefer using specific automaton types such as [`DBA`]/[`DPA`] etc.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum OmegaAcceptanceCondition {
    /// Parity condition of the given [`ParityKind`] on the priorities `low..=high` (usually
    /// `0..=n`). For [`ParityKind::MinEven`], the smallest priority that is seen infinitely often
    /// has to be even.
    Parity(ParityKind, Int, Int),
    /// Büchi condition: the edges in acceptance set `0` are seen infinitely often.
    Buchi,
    /// Rabin condition: accepting if for at least one pair, no acceptance set in `fin` and at
    /// least one acceptance set in `inf` is seen infinitely often (`Fin(fin) & Inf(inf)`).
    /// An empty list of pairs rejects everything.
    Rabin(Vec<RabinPair<Int>>),
    /// Streett condition: accepting if for every pair, no acceptance set in `fin` or at least
    /// one acceptance set in `inf` is seen infinitely often (`Fin(fin) | Inf(inf)`). An empty
    /// list of pairs accepts everything.
    Streett(Vec<RabinPair<Int>>),
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
    pub fn satisfied(&self, infset: &BTreeSet<AcceptanceMask>) -> Result<bool, Error> {
        match self {
            OmegaAcceptanceCondition::Parity(kind, low, high) => {
                let decisive = kind.decisive(Self::priorities(infset, *low, *high)?);
                Ok(decisive.is_some_and(|x| x.is_multiple_of(2) == kind.is_even()))
            }
            OmegaAcceptanceCondition::Buchi | OmegaAcceptanceCondition::Reachability => {
                Ok(infset.iter().any(AcceptanceMask::as_bool))
            }
            OmegaAcceptanceCondition::CoBuchi | OmegaAcceptanceCondition::Safety => {
                Ok(!infset.iter().any(AcceptanceMask::as_bool))
            }
            OmegaAcceptanceCondition::Rabin(pairs) => {
                let seen = Self::seen_sets(infset);
                Ok(pairs
                    .iter()
                    .any(|p| p.fin.is_disjoint(&seen) && !p.inf.is_disjoint(&seen)))
            }
            OmegaAcceptanceCondition::Streett(pairs) => {
                let seen = Self::seen_sets(infset);
                Ok(pairs
                    .iter()
                    .all(|p| p.fin.is_disjoint(&seen) || !p.inf.is_disjoint(&seen)))
            }
        }
    }

    /// The acceptance sets that occur in at least one of the masks.
    fn seen_sets(infset: &BTreeSet<AcceptanceMask>) -> BTreeSet<Int> {
        infset.iter().flat_map(AcceptanceMask::iter).collect()
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

/// Evaluates the condition on the masks of the edges that a run takes infinitely often. A run
/// whose masks are malformed for the condition, e.g. a parity edge without a priority, is
/// rejecting. Use [`OmegaAcceptanceCondition::satisfied`] to see the error instead.
impl<T, W> Semantics<T, W> for OmegaAcceptanceCondition
where
    T: Deterministic<EdgeColor = AcceptanceMask>,
    W: OmegaWord<Symbol = SymbolOf<T>>,
{
    type Output = bool;
    fn output(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<bool> {
        let inf = observe_omega::<T, W, run::EdgeColorSet<T>>(ts, initial, word)?;
        let infset: BTreeSet<_> = inf.0.into_iter().collect();
        Some(self.satisfied(&infset).unwrap_or_else(|error| {
            tracing::warn!("rejecting a run with malformed acceptance sets: {error}");
            false
        }))
    }
}

/// Malformed masks (for example a parity edge without a priority) make the colors rejecting, like
/// for the deterministic [`Semantics`].
impl CycleCondition for OmegaAcceptanceCondition {
    type Color = AcceptanceMask;
    fn satisfied_by(&self, colors: &math::FxIndexSet<AcceptanceMask>) -> bool {
        self.satisfied(&colors.iter().cloned().collect())
            .unwrap_or(false)
    }
    fn avoid(&self, colors: &math::FxIndexSet<AcceptanceMask>) -> Vec<Vec<AcceptanceMask>> {
        let masks_where = |keep: &dyn Fn(&AcceptanceMask) -> bool| -> Vec<AcceptanceMask> {
            colors.iter().filter(|mask| keep(mask)).cloned().collect()
        };
        let priorities =
            |low, high| Self::priorities(&colors.iter().cloned().collect(), low, high).ok();
        match self {
            Self::Buchi | Self::Reachability => Vec::new(),
            Self::CoBuchi | Self::Safety => vec![masks_where(&AcceptanceMask::as_bool)],
            // every cycle through the decisive priority of the component has the wrong parity
            Self::Parity(kind, low, high) => {
                match priorities(*low, *high).and_then(|p| kind.decisive(p)) {
                    Some(decisive) => {
                        vec![masks_where(&|m| m.try_as_priority().ok() == Some(decisive))]
                    }
                    None => Vec::new(),
                }
            }
            Self::Rabin(pairs) => pairs
                .iter()
                .filter(|pair| {
                    colors
                        .iter()
                        .any(|m| m.iter().any(|set| pair.inf.contains(&set)))
                })
                .map(|pair| masks_where(&|m| m.iter().any(|set| pair.fin.contains(&set))))
                .collect(),
            // shortcut: Streett falls back to leaving out each mask in turn (exponential), a
            // dedicated Emerson-Lei decomposition would be polynomial in the number of pairs
            Self::Streett(_) => colors.iter().map(|mask| vec![mask.clone()]).collect(),
        }
    }
}

impl<A: Alphabet> Automaton<NTS<A, Int, AcceptanceMask>, Existential<OmegaAcceptanceCondition>> {
    /// Creates a new instance from the given transition system, initial state and
    /// acceptance condition.
    pub fn new(
        ts: NTS<A, Int, AcceptanceMask>,
        initial: DefaultIdType,
        acceptance: OmegaAcceptanceCondition,
    ) -> Self {
        Automaton {
            ts,
            initial,
            acceptance: Existential(acceptance),
        }
    }

    /// Attempts to convert `self` into a [`DeterministicOmegaAutomaton`]. Returns
    /// `self` unchanged as the error if this is not possible because the transition system
    /// underlying `self` is not deterministic.
    pub fn try_into_deterministic(self) -> Result<DeterministicOmegaAutomaton<A>, Self> {
        let Automaton {
            ts,
            initial,
            acceptance,
        } = self;
        match ts.try_into_deterministic() {
            Ok(dts) => Ok(DeterministicOmegaAutomaton::new(dts, initial, acceptance.0)),
            Err(ts) => Err(Self {
                ts,
                initial,
                acceptance,
            }),
        }
    }
}

impl<A: Alphabet> Automaton<DTS<A, Int, AcceptanceMask>, OmegaAcceptanceCondition> {
    /// Creates a new instance from the given transition system, initial state and
    /// acceptance condition.
    pub fn new(
        ts: DTS<A, Int, AcceptanceMask>,
        initial: DefaultIdType,
        acceptance: OmegaAcceptanceCondition,
    ) -> Self {
        Automaton {
            ts,
            initial,
            acceptance,
        }
    }

    /// Verifies that every edge has exactly one acceptance set and that the corresponding
    /// priority lies within `low..=high`.
    fn check_priorities(&self, low: Int, high: Int) -> Result<(), AcceptanceError> {
        for q in self.ts.states() {
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
    /// A [`DPA`] is min-even, so the other [`ParityKind`]s are converted by renumbering the
    /// priorities (`p + 1` for min odd, `c - p` for the max kinds); if the result needs a
    /// priority above [`Int::MAX`] an [`Error::Acceptance`] is returned.
    ///
    /// [`OmegaAcceptanceCondition::Reachability`] and [`OmegaAcceptanceCondition::Safety`] are
    /// converted like [`OmegaAcceptanceCondition::Buchi`] and
    /// [`OmegaAcceptanceCondition::CoBuchi`], respectively.
    ///
    /// The conversion is not implemented for [`OmegaAcceptanceCondition::Rabin`] and
    /// [`OmegaAcceptanceCondition::Streett`]; these yield [`Error::NotYetImplemented`].
    pub fn into_dpa(self) -> Result<DPA<DTS<A, Void, Int>>, Error> {
        if let OmegaAcceptanceCondition::Parity(_, low, high) = self.acceptance {
            self.check_priorities(low, high)?;
        }
        match &self.acceptance {
            OmegaAcceptanceCondition::Parity(kind, low, high) => {
                // A DPA is min-even. A max kind maps the priority `p` to `c - p`, where `c >= high`
                // has the parity that makes `c - max` even iff the run is accepting; min odd maps
                // `p` to `p + 1`. The priorities have been validated at the start of this function.
                let (low, high) = (usize::from(*low), usize::from(*high));
                let c = high + usize::from((high % 2 == 0) != kind.is_even());
                let largest = match kind {
                    ParityKind::MinEven => high,
                    ParityKind::MinOdd => high + 1,
                    ParityKind::MaxEven | ParityKind::MaxOdd => c - low,
                };
                if largest > usize::from(Int::MAX) {
                    return Err(AcceptanceError::PriorityOverflow { needed: largest }.into());
                }
                let to_new = |p: usize| match kind {
                    ParityKind::MinEven => p,
                    ParityKind::MinOdd => p + 1,
                    ParityKind::MaxEven | ParityKind::MaxOdd => c - p,
                } as Int;
                Ok(self
                    .ts
                    .map_edge_colors(|mask| to_new(usize::from(mask.as_priority())))
                    .with_initial(self.initial)
                    .erase_state_colors()
                    .collect())
            }
            OmegaAcceptanceCondition::Buchi | OmegaAcceptanceCondition::Reachability => Ok(self
                .ts
                .map_edge_colors(|mask| if mask.as_bool() { 0 } else { 1 })
                .with_initial(self.initial)
                .erase_state_colors()
                .collect()),
            OmegaAcceptanceCondition::CoBuchi | OmegaAcceptanceCondition::Safety => Ok(self
                .ts
                // a run is accepting iff it sees the bad edges (priority 1) only finitely often,
                // i.e. iff the least priority seen infinitely often is the even 2
                .map_edge_colors(|mask| if mask.as_bool() { 1 } else { 2 })
                .with_initial(self.initial)
                .erase_state_colors()
                .collect()),
            OmegaAcceptanceCondition::Rabin(_) => Err(Error::NotYetImplemented(
                "conversion of Rabin automata into DPA",
            )),
            OmegaAcceptanceCondition::Streett(_) => Err(Error::NotYetImplemented(
                "conversion of Streett automata into DPA",
            )),
        }
    }
}

impl From<DeterministicOmegaAutomaton<PropAlphabet>> for DeterministicOmegaAutomaton<CharAlphabet> {
    fn from(value: DeterministicOmegaAutomaton<PropAlphabet>) -> Self {
        // the states are numbered consecutively, in the order of `states`
        let ids: BTreeMap<_, u32> = value
            .states()
            .enumerate()
            .map(|(n, q)| (q, n as u32))
            .collect();
        let ts = Builder::default()
            .with_state_colors(
                value
                    .states()
                    .filter_map(|q| Some(value.state_color(q)?.into_owned())),
            )
            .with_transitions(value.states().flat_map(|q| {
                value.edges_from(q).into_iter().flatten().flat_map(|edge| {
                    let (source, target) = (ids[&edge.source()], ids[&edge.target()]);
                    edge.expression()
                        .chars_iter()
                        .map(move |sym| (source, sym, edge.color().clone(), target))
                })
            }))
            .into_dts();
        let initial = crate::ts::StateId::from(ids[&value.initial()]);
        DeterministicOmegaAutomaton::new(ts, initial, value.acceptance)
    }
}

impl TryFrom<DeterministicOmegaAutomaton<CharAlphabet>>
    for DeterministicOmegaAutomaton<PropAlphabet>
{
    /// For now, we allow this to error out in exactly one case: if the number of alphabet symbols
    /// is not a power of 2 and cannot be mapped immediately into AP combinations.
    type Error = PropAlphabetError;
    fn try_from(value: DeterministicOmegaAutomaton<CharAlphabet>) -> Result<Self, Self::Error> {
        let mut ts = DTS::for_alphabet(PropAlphabet::try_from_char_alphabet(value.alphabet())?);

        // the states are numbered consecutively, in the order of `states`
        let mut ids = BTreeMap::new();
        for q in value.states() {
            if let Some(color) = value.state_color(q) {
                ids.insert(q, ts.add_state(color.into_owned()));
            }
        }

        for q in value.states() {
            for edge in value.edges_from(q).into_iter().flatten() {
                let (Some(&source), Some(&target)) =
                    (ids.get(&edge.source()), ids.get(&edge.target()))
                else {
                    continue;
                };
                ts.add_edge((
                    source,
                    ts.alphabet()
                        .make_expression(ts.alphabet().char_to_symbol(*edge.expression())),
                    edge.color().clone(),
                    target,
                ));
            }
        }

        let initial = *ids
            .get(&value.initial())
            .expect("the initial state of an automaton is one of its states");
        Ok(DeterministicOmegaAutomaton::new(
            ts,
            initial,
            value.acceptance,
        ))
    }
}

/// Helpers for tests that compare automata on many words.
#[cfg(test)]
pub(crate) mod testing {
    use super::*;

    /// A small deterministic pseudo random number generator (xorshift).
    pub(crate) struct Rng(pub(crate) u64);

    impl Rng {
        pub(crate) fn below(&mut self, n: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % n as u64) as usize
        }
    }

    /// A complete deterministic automaton over `a, b` with `states` states whose edge masks are
    /// drawn by `mask`.
    pub(crate) fn random_automaton(
        rng: &mut Rng,
        states: usize,
        acceptance: OmegaAcceptanceCondition,
        mut mask: impl FnMut(&mut Rng) -> AcceptanceMask,
    ) -> DeterministicOmegaAutomaton<CharAlphabet> {
        let mut ts: DTS<CharAlphabet, Int, AcceptanceMask> =
            DTS::for_alphabet(CharAlphabet::of_size(2));
        let ids: Vec<_> = (0..states).map(|_| ts.add_state(0)).collect();
        for &q in &ids {
            for sym in ['a', 'b'] {
                let target = ids[rng.below(states)];
                ts.add_edge((q, sym, mask(rng), target));
            }
        }
        DeterministicOmegaAutomaton::new(ts, ids[0], acceptance)
    }

    /// The lassos `u v^ω` over `a, b` with `|u| <= 2` and `1 <= |v| <= 3`.
    pub(crate) fn lassos() -> Vec<crate::word::ReducedOmegaWord<char>> {
        let words = |max: usize| -> Vec<String> {
            let mut all = vec![String::new()];
            let mut layer = vec![String::new()];
            for _ in 0..max {
                layer = layer
                    .iter()
                    .flat_map(|w| ["a", "b"].map(|c| format!("{w}{c}")))
                    .collect();
                all.extend(layer.clone());
            }
            all
        };
        let mut out = vec![];
        for u in words(2) {
            for v in words(3).into_iter().filter(|v| !v.is_empty()) {
                out.push(crate::upw!(u.as_str(), v.as_str()));
            }
        }
        out
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
        use OmegaAcceptanceCondition::Parity;
        use ParityKind::*;
        assert_eq!(Parity(MinEven, 0, 2).satisfied(&infset(&[])), Ok(false));
        assert_eq!(
            Parity(MinEven, 0, 2).satisfied(&infset(&[&[0], &[1]])),
            Ok(true)
        );
        assert_eq!(
            Parity(MinEven, 0, 2).satisfied(&infset(&[&[1], &[2]])),
            Ok(false)
        );
        assert_eq!(
            Parity(MaxEven, 0, 2).satisfied(&infset(&[&[2], &[1]])),
            Ok(true)
        );
        assert_eq!(
            Parity(MaxEven, 0, 2).satisfied(&infset(&[&[0], &[1]])),
            Ok(false)
        );
        assert_eq!(Parity(MaxEven, 0, 2).satisfied(&infset(&[])), Ok(false));
        assert_eq!(
            Parity(MinEven, 0, 2).satisfied(&infset(&[&[3]])),
            Err(Error::Acceptance(AcceptanceError::PriorityOutOfRange {
                priority: 3,
                low: 0,
                high: 2
            }))
        );
        assert_eq!(
            Parity(MaxEven, 0, 2).satisfied(&infset(&[&[]])),
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
    fn satisfied_rabin_and_streett() {
        use OmegaAcceptanceCondition::{Rabin, Streett};
        let pairs = vec![
            RabinPair::from_iters([0], [1]),
            RabinPair::from_iters([], [2]),
        ];
        // Rabin: some pair has no `fin` set and some `inf` set
        assert_eq!(Rabin(pairs.clone()).satisfied(&infset(&[&[1]])), Ok(true));
        assert_eq!(
            Rabin(pairs.clone()).satisfied(&infset(&[&[0, 1]])),
            Ok(false)
        );
        assert_eq!(
            Rabin(pairs.clone()).satisfied(&infset(&[&[0], &[2]])),
            Ok(true)
        );
        assert_eq!(Rabin(pairs.clone()).satisfied(&infset(&[&[0]])), Ok(false));
        assert_eq!(Rabin(vec![]).satisfied(&infset(&[&[0]])), Ok(false));
        // Streett: every pair has no `fin` set or some `inf` set
        assert_eq!(Streett(pairs.clone()).satisfied(&infset(&[])), Ok(true));
        assert_eq!(
            Streett(pairs.clone()).satisfied(&infset(&[&[0]])),
            Ok(false)
        );
        assert_eq!(
            Streett(pairs.clone()).satisfied(&infset(&[&[0, 1, 2]])),
            Ok(true)
        );
        assert_eq!(Streett(vec![]).satisfied(&infset(&[])), Ok(true));
    }

    /// `into_dpa` and `satisfied` have to agree on a one-state automaton that loops on `mask`.
    #[test]
    fn into_dpa_agrees_with_satisfied() {
        use OmegaAcceptanceCondition::*;
        use ParityKind::*;
        let cases = [
            (Parity(MinEven, 0, 2), vec![0], true),
            (Parity(MinEven, 0, 2), vec![1], false),
            (Parity(MaxEven, 0, 2), vec![2], true),
            (Parity(MaxEven, 0, 2), vec![1], false),
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

            let word = crate::upw!("a");
            let aut = two_state_automaton(acc.clone(), mask);
            assert_eq!(aut.accepts(&word), expected, "{acc:?}");
            let dpa = aut.into_dpa().unwrap();
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
    fn satisfied_all_parity_kinds() {
        use OmegaAcceptanceCondition::Parity;
        use ParityKind::*;
        // the priorities 1 and 2 are seen infinitely often: min is 1, max is 2
        let seen = infset(&[&[1], &[2]]);
        assert_eq!(Parity(MinEven, 0, 3).satisfied(&seen), Ok(false));
        assert_eq!(Parity(MinOdd, 0, 3).satisfied(&seen), Ok(true));
        assert_eq!(Parity(MaxEven, 0, 3).satisfied(&seen), Ok(true));
        assert_eq!(Parity(MaxOdd, 0, 3).satisfied(&seen), Ok(false));
        for kind in [MinEven, MinOdd, MaxEven, MaxOdd] {
            assert_eq!(
                Parity(kind, 0, 3).satisfied(&infset(&[])),
                Ok(false),
                "{kind:?}"
            );
        }
    }

    /// `into_dpa` has to give the same language as the original, for every parity kind and for
    /// ranges that do not start at 0.
    #[test]
    fn into_dpa_agrees_with_satisfied_on_random_parity_automata() {
        use OmegaAcceptanceCondition::Parity;
        use ParityKind::*;
        use testing::*;
        let lassos = lassos();
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        for kind in [MinEven, MinOdd, MaxEven, MaxOdd] {
            for (low, high) in [(0, 3), (0, 4), (1, 4), (2, 3), (1, 1)] {
                for _ in 0..6 {
                    let acc = Parity(kind, low, high);
                    let aut = random_automaton(&mut rng, 3, acc.clone(), |rng| {
                        AcceptanceMask::from_iter([
                            low + rng.below((high - low) as usize + 1) as Int
                        ])
                    });
                    let dpa = aut.clone().into_dpa().unwrap();
                    for word in &lassos {
                        assert_eq!(dpa.accepts(word), aut.accepts(word), "{acc:?} {word:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn into_dpa_rejects_priorities_that_do_not_fit() {
        use OmegaAcceptanceCondition::Parity;
        use ParityKind::*;
        let overflow = |kind, low, high| {
            two_state_automaton(Parity(kind, low, high), AcceptanceMask::from_iter([high]))
                .into_dpa()
                .err()
        };
        assert_eq!(
            overflow(MinOdd, 0, Int::MAX),
            Some(Error::Acceptance(AcceptanceError::PriorityOverflow {
                needed: 256
            }))
        );
        // c = 256 for max even with an odd high
        assert_eq!(
            overflow(MaxEven, 0, Int::MAX),
            Some(Error::Acceptance(AcceptanceError::PriorityOverflow {
                needed: 256
            }))
        );
        assert!(overflow(MaxEven, 1, Int::MAX).is_none());
        assert!(overflow(MinEven, 0, Int::MAX).is_none());
        assert!(overflow(MaxOdd, 0, Int::MAX).is_none());
    }

    #[test]
    fn into_dpa_co_buchi_with_both_kinds_infinitely_often() {
        use OmegaAcceptanceCondition::{CoBuchi, Safety};
        // `a` is a bad edge, `b` is a good one; from the loop on `b` we can go back via `a`
        let mut ts: DTS<CharAlphabet, Int, AcceptanceMask> =
            DTS::for_alphabet(CharAlphabet::of_size(2));
        let q = ts.add_state(0);
        ts.add_edge((q, 'a', AcceptanceMask::from_iter([0]), q));
        ts.add_edge((q, 'b', AcceptanceMask::from_iter([]), q));
        for acc in [CoBuchi, Safety] {
            let aut = DeterministicOmegaAutomaton::new(ts.clone(), q, acc.clone());
            let dpa = aut.clone().into_dpa().unwrap();
            for word in [
                crate::upw!("a"),
                crate::upw!("b"),
                crate::upw!("ab"),
                crate::upw!("b", "a"),
                crate::upw!("a", "b"),
                crate::upw!("bba"),
            ] {
                assert_eq!(dpa.accepts(&word), aut.accepts(&word), "{acc:?} {word:?}");
            }
            assert!(!dpa.accepts(crate::upw!("ab")));
            assert!(dpa.accepts(crate::upw!("a", "b")));
        }
    }

    #[test]
    fn into_dpa_validates_priorities() {
        use crate::automaton::AcceptanceError;

        let parity = || OmegaAcceptanceCondition::Parity(ParityKind::MinEven, 0, 2);
        assert!(
            two_state_automaton(parity(), AcceptanceMask::from_iter([1]))
                .into_dpa()
                .is_ok()
        );
        assert_eq!(
            two_state_automaton(parity(), AcceptanceMask::from_iter([]))
                .into_dpa()
                .err(),
            Some(Error::Acceptance(AcceptanceError::NoAcceptanceSet))
        );
        assert_eq!(
            two_state_automaton(parity(), AcceptanceMask::from_iter([0, 1]))
                .into_dpa()
                .err(),
            Some(Error::Acceptance(AcceptanceError::MultipleAcceptanceSets(
                vec![0, 1]
            )))
        );
        assert_eq!(
            two_state_automaton(parity(), AcceptanceMask::from_iter([5]))
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
                OmegaAcceptanceCondition::Parity(ParityKind::MaxEven, 1, 3),
                AcceptanceMask::from_iter([2])
            )
            .into_dpa()
            .is_ok()
        );
    }

    #[test]
    fn into_dpa_reports_unsupported_conditions() {
        for unsupported in [
            OmegaAcceptanceCondition::Rabin(vec![]),
            OmegaAcceptanceCondition::Streett(vec![]),
        ] {
            assert!(matches!(
                single_state_automaton(unsupported).into_dpa(),
                Err(Error::NotYetImplemented(_))
            ));
        }
        for supported in [
            OmegaAcceptanceCondition::Buchi,
            OmegaAcceptanceCondition::CoBuchi,
            OmegaAcceptanceCondition::Parity(ParityKind::MinEven, 0, 1),
            OmegaAcceptanceCondition::Reachability,
            OmegaAcceptanceCondition::Safety,
        ] {
            assert!(single_state_automaton(supported).into_dpa().is_ok());
        }
    }
}
