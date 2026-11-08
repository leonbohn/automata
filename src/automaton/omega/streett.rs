use std::collections::BTreeSet;

use super::RabinPair;
use crate::automaton::semantics::observe_omega;
use crate::automaton::{Automaton, Semantics};
use crate::automaton::{CycleCondition, Existential};
use crate::ts::{Deterministic, EdgeColor, StateIndex, SymbolOf, run};
use crate::word::OmegaWord;
use crate::{Color, Int, Void, alphabet::CharAlphabet};
use crate::{DTS, NTS, math};
use std::hash::Hash;

/// A deterministic Streett automaton (DSA) uses a [`StreettCondition`] to determine acceptance, the
/// dual of a [`super::DRA`]. Such a condition consists of a set of [`RabinPair`]s, which in turn
/// are made up of a set `fin` and a set `inf`. A pair is satisfied by an infinite run if some
/// color from `fin` is visited only finitely often or some color from `inf` is visited
/// infinitely often (a request in `fin` is answered by a response in `inf`). Overall, a Streett
/// condition is satisfied if *all* of its pairs are satisfied; without pairs it is always
/// satisfied.
///
/// ```
/// use automata::prelude::*;
/// use automata::automaton::{RabinPair, StreettCondition};
///
/// // every `a` is eventually answered by a `b`: the pair is `fin = {a-edges}, inf = {b-edges}`
/// let pair = RabinPair::from_iters([0], [1]);
/// let dsa = DSA::from_parts_with_acceptance(
///     Builder::without_state_colors()
///         .with_transitions([(0, 'a', 0, 0), (0, 'b', 1, 0)])
///         .into_dts(),
///     q(0),
///     [pair].into(),
/// );
/// assert!(dsa.accepts(upw!("b")) && dsa.accepts(upw!("ab")));
/// assert!(!dsa.accepts(upw!("bb", "a")));
/// ```
pub type DSA<T = DTS<CharAlphabet, Void, Int>> = Automaton<T, StreettCondition<EdgeColor<T>>>;

/// A nondeterministic Streett automaton (NSA): it accepts an infinite word if *some* run on it
/// satisfies the [`StreettCondition`], see [`Existential`].
pub type NSA<T = NTS<CharAlphabet, Void, Int>> =
    Automaton<T, Existential<StreettCondition<EdgeColor<T>>>>;

/// Represents a Streett condition, which is a set of [`RabinPair`]s. Such a condition is satisfied
/// if all of its pairs are satisfied, where a pair is satisfied by a set of colors if it contains
/// no element of `fin` or at least one element of `inf`.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct StreettCondition<C: Color + Ord>(BTreeSet<RabinPair<C>>);

impl<C, I> From<I> for StreettCondition<C>
where
    C: Color + Ord,
    I: IntoIterator<Item = RabinPair<C>>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl<C: Color + Ord> StreettCondition<C> {
    /// Iterates over the pairs of the condition, in increasing order.
    pub fn pairs(&self) -> impl Iterator<Item = &RabinPair<C>> {
        self.0.iter()
    }

    /// Returns true if and only if all pairs are satisfied by the given set of colors, i.e. if for
    /// every pair the set contains no color from `fin` or at least one color from `inf`.
    pub fn satisfied_by_set(&self, colors: &BTreeSet<C>) -> bool {
        self.0
            .iter()
            .all(|pair| pair.fin.is_disjoint(colors) || !pair.inf.is_disjoint(colors))
    }
}

impl<T, W> Semantics<T, W> for StreettCondition<EdgeColor<T>>
where
    T: Deterministic,
    W: OmegaWord<Symbol = SymbolOf<T>>,
    EdgeColor<T>: Color + Ord + Eq + Hash,
{
    type Output = bool;
    fn output(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<bool> {
        let inf = observe_omega::<T, W, run::EdgeColorSet<T>>(ts, initial, word)?.0;
        Some(self.satisfied_by_set(&inf.iter().cloned().collect()))
    }
}

impl<C: Color + Ord + Hash> CycleCondition for StreettCondition<C> {
    type Color = C;
    fn satisfied_by(&self, colors: &math::FxIndexSet<C>) -> bool {
        self.satisfied_by_set(&colors.iter().cloned().collect())
    }
    fn avoid(&self, colors: &math::FxIndexSet<C>) -> Vec<Vec<C>> {
        // A pair is violated by the component if it sees a `fin` color but no `inf` color. A good
        // cycle then cannot see any `inf` color, so it has to avoid the `fin` colors of every
        // violated pair, all of which are removed at once.
        let violated = self.0.iter().filter(|pair| {
            colors.iter().any(|c| pair.fin.contains(c))
                && !colors.iter().any(|c| pair.inf.contains(c))
        });
        let mut avoided: Vec<C> = Vec::new();
        for pair in violated {
            for color in colors.iter().filter(|c| pair.fin.contains(*c)) {
                if !avoided.contains(color) {
                    avoided.push(color.clone());
                }
            }
        }
        vec![avoided]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automaton::omega::testing::{Rng, lassos, random_automaton};
    use crate::automaton::{AcceptanceMask, Emptiness, OmegaAcceptanceCondition, ParityKind};
    use crate::ts::{Builder, q};

    #[test]
    fn streett_condition_on_sets() {
        let cond: StreettCondition<Int> = [
            RabinPair::from_iters([0], [1]),
            RabinPair::from_iters([2], []),
        ]
        .into();
        let set = |colors: &[Int]| colors.iter().copied().collect::<BTreeSet<_>>();
        assert!(cond.satisfied_by_set(&set(&[])));
        assert!(cond.satisfied_by_set(&set(&[1])));
        assert!(cond.satisfied_by_set(&set(&[0, 1])));
        assert!(!cond.satisfied_by_set(&set(&[0])));
        // the second pair can only be satisfied by never seeing 2
        assert!(!cond.satisfied_by_set(&set(&[1, 2])));
        assert!(StreettCondition::<Int>::default().satisfied_by_set(&set(&[0, 1, 2])));
    }

    #[test]
    fn streett_automata() {
        let ts = Builder::without_state_colors()
            .with_transitions([
                (0, 'a', 0, 0),
                (0, 'b', 1, 1),
                (1, 'a', 0, 0),
                (1, 'b', 1, 1),
            ])
            .into_dts();
        let dsa = DSA::from_parts_with_acceptance(
            ts.clone(),
            q(0),
            [RabinPair::from_iters([0], [1])].into(),
        );
        assert!(dsa.accepts(upw!("ba")));
        assert!(!dsa.accepts(upw!("b", "a")));
        assert!(dsa.accepts(upw!("a", "b")));
        // no pairs: everything is accepted
        let all = DSA::from_parts_with_acceptance(ts, q(0), StreettCondition::default());
        assert!(all.accepts(upw!("a")) && all.accepts(upw!("ab")));
        assert!(Emptiness::of(&all).witness().is_some());
    }

    #[test]
    fn nondeterministic_streett_automata_and_emptiness() {
        // an `a` can leave state 0 for the state 1, where `a` is answered forever (color 1)
        let nsa = NSA::from_parts_with_acceptance(
            Builder::without_state_colors()
                .with_transitions([
                    (0, 'a', 0, 0),
                    (0, 'b', 0, 0),
                    (0, 'a', 1, 1),
                    (1, 'a', 1, 1),
                ])
                .into_nts(),
            q(0),
            Existential([RabinPair::from_iters([0], [1])].into()),
        );
        assert!(nsa.accepts(upw!("b", "a")) && nsa.accepts(upw!("a")));
        assert!(!nsa.accepts(upw!("ab")) && !nsa.accepts(upw!("b")));
        let witness = Emptiness::of(&nsa).witness().unwrap();
        assert!(nsa.accepts(&witness));
        let empty = NSA::from_parts_with_acceptance(
            Builder::without_state_colors()
                .with_transitions([(0, 'a', 0, 0)])
                .into_nts(),
            q(0),
            Existential([RabinPair::from_iters([0], [1])].into()),
        );
        assert!(Emptiness::of(&empty).holds());
    }

    /// The typed condition agrees with `OmegaAcceptanceCondition::Streett` on random automata
    /// whose edges are in exactly one acceptance set, for `accepts`, the nondeterministic
    /// reading of the same automaton and `Emptiness`.
    #[test]
    fn typed_condition_agrees_with_omega_acceptance_condition() {
        let lassos = lassos();
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for _ in 0..60 {
            let pair_count = 1 + rng.below(3);
            let pairs: Vec<RabinPair<Int>> = (0..pair_count)
                .map(|_| {
                    let subset = |rng: &mut Rng| {
                        (0..4 as Int)
                            .filter(|_| rng.below(3) == 0)
                            .collect::<Vec<_>>()
                    };
                    RabinPair::from_iters(subset(&mut rng), subset(&mut rng))
                })
                .collect();
            let states = 1 + rng.below(4);
            let omega = random_automaton(
                &mut rng,
                states,
                OmegaAcceptanceCondition::Parity(ParityKind::MinEven, 0, 3),
                |rng| AcceptanceMask::from_iter([rng.below(4) as Int]),
            );
            // the priority is the acceptance set, so this has the colors of `omega`
            let colored = omega.clone().into_dpa().unwrap();
            let dsa: DSA<_> = colored.map_acceptance(|_| StreettCondition::from(pairs.clone()));
            let nsa = dsa.clone().map_acceptance(Existential);
            let omega = omega.map_acceptance(|_| OmegaAcceptanceCondition::Streett(pairs.clone()));
            let mut some_accepted = false;
            for word in &lassos {
                let expected = omega.accepts(word);
                assert_eq!(dsa.accepts(word), expected, "{pairs:?} {word:?}");
                assert_eq!(nsa.accepts(word), expected, "{pairs:?} {word:?}");
                some_accepted |= expected;
            }
            match Emptiness::of(&dsa).witness() {
                Some(witness) => assert!(omega.accepts(&witness), "{pairs:?} {witness:?}"),
                None => assert!(!some_accepted, "{pairs:?}"),
            }
            assert_eq!(
                Emptiness::of(&nsa).witness().is_some(),
                Emptiness::of(&dsa).witness().is_some()
            );
        }
    }
}
