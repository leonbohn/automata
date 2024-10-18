use core::fmt;
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet, VecDeque},
    ops::{Deref, DerefMut},
};

use automata::{
    math::{self, Equivalent},
    prelude::{Alphabet, CharAlphabet, Show, SimpleAlphabet, Sproutable, Symbol},
    RightCongruence, TransitionSystem, Void,
};
use itertools::Itertools;
use tracing::trace;

#[derive(Clone, Eq, PartialEq)]
pub struct Factor<S>(Vec<S>);

impl<S> Factor<S> {
    pub fn without_last(&self) -> Option<Self>
    where
        S: Clone,
    {
        if self.is_empty() {
            return None;
        }
        Some(Self(self.0[..self.len() - 1].to_vec()))
    }
}

impl<S> Deref for Factor<S> {
    type Target = Vec<S>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<S> DerefMut for Factor<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<S> FromIterator<S> for Factor<S> {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<S: Symbol> fmt::Debug for Factor<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for sym in self.0.iter().map(|sym| sym.show()) {
            f.write_str(&sym)?;
        }
        Ok(())
    }
}

impl<S: Symbol> Ord for Factor<S> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.len().cmp(&other.0.len()).then(
            self.0
                .iter()
                .zip(other.0.iter())
                .find_map(|(l, r)| {
                    let ord = l.cmp(r);
                    if ord != Ordering::Equal {
                        Some(ord)
                    } else {
                        None
                    }
                })
                .unwrap_or(Ordering::Equal),
        )
    }
}
impl<S: Symbol> PartialOrd for Factor<S> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone)]
pub struct Split<S: Symbol>([Factor<S>; 2]);

impl<S: Symbol> Equivalent<Split<S>> for (&Vec<S>, &Vec<S>) {
    fn equivalent(&self, key: &Split<S>) -> bool {
        self.0 == &key.0[0].0 && self.1 == &key.0[1].0
    }
}

impl<S: Symbol> Split<S> {
    pub fn shave_right(&self) -> Option<Split<S>> {
        let [ref a, ref b] = self.0;
        if a.last()? == b.last()? {
            Some(Split::new(
                a.without_last().expect("we know the last symbol exists"),
                b.without_last().expect("we know the last symbol exists"),
            ))
        } else {
            None
        }
    }

    #[inline(always)]
    pub(crate) fn assert_ordered(&self) {
        if cfg!(debug_assertions) {
            assert!(
                !(self.0[0] > self.0[1]),
                "Incongruence pair must be ordered"
            );
        }
    }
    pub fn new(a: Factor<S>, b: Factor<S>) -> Self {
        if a < b {
            Split([a, b])
        } else {
            Split([b, a])
        }
    }
}

impl<S: Symbol> fmt::Debug for Split<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} | {:?}", self.0[0], self.0[1])
    }
}

impl Split<char> {
    pub fn from_words(first: &str, second: &str) -> Self {
        Self::new(first.chars().collect(), second.chars().collect())
    }
}

impl<S: Symbol> PartialOrd for Split<S> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.assert_ordered();
        other.assert_ordered();
        self.0[0]
            .partial_cmp(&other.0[0])
            .or_else(|| self.0[1].partial_cmp(&other.0[1]))
    }
}

impl<S: Symbol> Eq for Split<S> {}
impl<S: Symbol> PartialEq for Split<S> {
    fn eq(&self, other: &Self) -> bool {
        self.assert_ordered();
        other.assert_ordered();
        self.0 == other.0
    }
}

#[derive(Debug, Clone)]
pub struct Incongruence<A: Alphabet = CharAlphabet> {
    splits: Vec<Split<A::Symbol>>,
}

impl<A: Alphabet> FromIterator<Split<A::Symbol>> for Incongruence<A> {
    fn from_iter<T: IntoIterator<Item = Split<A::Symbol>>>(iter: T) -> Self {
        Self {
            splits: iter.into_iter().collect(),
        }
    }
}

impl<A: Alphabet> Incongruence<A> {
    pub fn refine(self) -> RefinedIncongruence<A> {
        let original_size = self.splits.len();
        let mut splits = self.splits;

        let mut current_index = 0;
        while current_index < splits.len() {
            trace!(
                "iteration {current_index}, considering {:?}",
                splits[current_index]
            );
            current_index += 1;
            if let Some(new) = splits[current_index - 1].shave_right() {
                trace!("adding split {:?}", new);
                splits.push(new)
            }
        }
        RefinedIncongruence {
            splits,
            actual: original_size,
        }
    }
    pub fn position<X: Equivalent<Split<A::Symbol>>>(&self, element: &X) -> Option<usize> {
        self.splits
            .iter()
            .enumerate()
            .find_map(|(i, x)| if element.equivalent(x) { Some(i) } else { None })
    }
    pub fn contains<X: Equivalent<Split<A::Symbol>>>(&self, element: &X) -> bool {
        self.position(element).is_some()
    }
}

#[derive(Debug, Clone)]
pub struct RefinedIncongruence<A: Alphabet> {
    splits: Vec<Split<A::Symbol>>,
    actual: usize,
}

impl<A: Alphabet> RefinedIncongruence<A> {
    pub fn position<X: Equivalent<Split<A::Symbol>>>(&self, element: &X) -> Option<usize> {
        self.splits
            .iter()
            .enumerate()
            .find_map(|(i, x)| if element.equivalent(x) { Some(i) } else { None })
    }
    pub fn contains<X: Equivalent<Split<A::Symbol>>>(&self, element: &X) -> bool {
        self.position(element).is_some()
    }
    pub fn as_right_congruence(&self) -> RightCongruence<A>
    where
        A: SimpleAlphabet,
    {
        let mut chars: HashSet<A::Symbol> = HashSet::new();
        for split in &self.splits {
            chars.extend(split.0[0].iter().chain(split.0[1].iter()));
        }
        trace!(
            "using alphabet {{{}}}",
            chars.iter().map(|chr| chr.show()).join(", ")
        );
        let alphabet = SimpleAlphabet::from_symbols(chars.clone());
        let mut rc = RightCongruence::new_with_initial_color(alphabet, Void);

        let mut mrs: math::Bijection<usize, Vec<A::Symbol>> =
            math::Bijection::from_iter([(0, vec![])]);
        let mut current_state_index = 0;
        while current_state_index < rc.size() {
            trace!(
                "considering state {current_state_index} {:?}",
                mrs.get_by_left(&current_state_index).unwrap()
            );
            'symbols: for &sym in &chars {
                let mut mtr = mrs.get_by_left(&current_state_index).unwrap().clone();
                mtr.push(sym);
                'target_search: for target in 0..=current_state_index {
                    let target_representative = mrs.get_by_left(&target).unwrap();
                    if !self.contains(&(target_representative, &mtr)) {
                        trace!(
                            "transition on {} to {target} {:?} is consistent",
                            sym.show(),
                            target_representative
                        );
                        // transition that is allowed
                        rc.add_edge((current_state_index as u32, sym, target as u32));
                        continue 'symbols;
                    } else {
                        trace!(
                            "transition on {} to {target} {:?} is notconsistent",
                            sym.show(),
                            target_representative
                        )
                    }
                }
                // no suitable target, add it
                let idx = rc.add_state(Void);
                trace!("adding new state {idx} {:?}", mtr);
                mrs.insert(idx as usize, mtr);
                rc.add_edge((current_state_index as u32, sym, idx));
            }
            current_state_index += 1;
            if current_state_index > 100 {
                panic!("somethign wong");
            }
        }

        rc
    }
}

#[cfg(test)]
mod tests {
    use automata::Dottable;

    use super::*;
    #[test]
    fn split_ordering() {
        let s1 = Split::from_words("ab", "aab");
        let s2 = Split::from_words("baa", "b");
        let s3 = Split::from_words("aa", "baaa");
        let s4 = Split::from_words("aab", "ab");

        assert!(s2 < s1);
        assert!(s4 == s1);
        assert!(s2 < s3);
    }

    #[test]
    fn incongruence_refinement() {
        let mut incongruence: Incongruence<CharAlphabet> = Incongruence::from_iter([
            Split::from_words("ab", "aab"),
            Split::from_words("baa", "b"),
            Split::from_words("aa", "baaa"),
            Split::from_words("aab", "ab"),
        ]);

        let refined = incongruence.refine();
        assert!(refined.contains(&Split::from_words("a", "aa")));
        assert!(refined.contains(&Split::from_words("", "ba")));
        assert!(refined.contains(&Split::from_words("", "a")));
    }

    #[test_log::test]
    fn incongruence_transition_system() {
        let mut incongruence: Incongruence<CharAlphabet> = Incongruence::from_iter([
            Split::from_words("ab", "aab"),
            Split::from_words("baa", "b"),
            Split::from_words("aa", "baaa"),
            Split::from_words("aab", "ab"),
        ]);

        let refined = incongruence.refine();
        let rc = refined.as_right_congruence();

        rc.display_rendered_graphviz();
        println!("{:?}", rc);
    }
}
