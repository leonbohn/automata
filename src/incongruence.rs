use std::{collections::VecDeque, fmt::Debug};

use automata_core::{
    math::{Map, Set},
    prelude::*,
};

pub trait WOFAlphabet: Alphabet {
    fn len(&self) -> Id;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn nth(&self, position: Id) -> Option<Self::Symbol>;
}

impl WOFAlphabet for CharAlphabet {
    fn len(&self) -> Id {
        Vec::len(self)
            .try_into()
            .expect("Cannot convert usize to Id type")
    }

    fn nth(&self, position: Id) -> Option<Self::Symbol> {
        let Some(sym) = self.as_ref().get(position as usize) else {
            panic!(
                "Index {position} is out of bounds, there are only {} symbols",
                self.len()
            );
        };
        Some(*sym)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Witness<S: Symbol = char>(pub(super) VecDeque<S>);

impl<S: Symbol> std::ops::Deref for Witness<S> {
    type Target = VecDeque<S>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<S: Symbol> std::borrow::Borrow<VecDeque<S>> for Witness<S> {
    fn borrow(&self) -> &VecDeque<S> {
        &self.0
    }
}
impl<S: Symbol> std::ops::DerefMut for Witness<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Word<S: Symbol = char>(pub(super) VecDeque<S>);

impl<S: Symbol> std::ops::Deref for Word<S> {
    type Target = VecDeque<S>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<S: Symbol> std::ops::DerefMut for Word<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl<S: Symbol> std::borrow::Borrow<VecDeque<S>> for Word<S> {
    fn borrow(&self) -> &VecDeque<S> {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Split<S: Symbol = char>(
    pub(super) Word<S>,
    pub(super) Word<S>,
    pub(super) Witness<S>,
);

impl<S: Symbol> Split<S> {
    pub fn refine(&mut self) -> bool {
        if self.0.len() == 0 || self.1.len() == 0 {
            return false;
        }
        if self.0.back() != self.1.back() {
            return false;
        }

        let sym = self.0.pop_back().expect("We know they're non-empty");
        assert_eq!(Some(sym), self.1.pop_back());

        // update the witness as it now needs to contain the symbol we popped
        self.2.push_front(sym);

        true
    }
}

pub enum MaybeTarget {
    Target(usize),
    Witness(usize),
}

pub struct Incongruence<A: WOFAlphabet = CharAlphabet> {
    pub(super) alphabet: A,
    pub(super) splits: Map<Split<A::Symbol>, bool>,
}
impl<I, J, K> FromIterator<(I, J, K)> for Incongruence
where
    I: FiniteWord<char>,
    J: FiniteWord<char>,
    K: FiniteWord<char>,
{
    fn from_iter<T: IntoIterator<Item = (I, J, K)>>(iter: T) -> Self {
        let splits: Map<_, _> = iter
            .into_iter()
            .map(|(u, v, z)| {
                (
                    Split(
                        Word(u.collect_deque()),
                        Word(v.collect_deque()),
                        Witness(z.collect_deque()),
                    ),
                    true,
                )
            })
            .collect();
        let alphabet = CharAlphabet::from_iter(
            splits
                .keys()
                .flat_map(|Split(u, v, z)| u.symbols().chain(v.symbols()).chain(z.symbols())),
        );
        Self { alphabet, splits }
    }
}

impl FromIterator<Split<char>> for Incongruence<CharAlphabet> {
    fn from_iter<T: IntoIterator<Item = Split<char>>>(iter: T) -> Self {
        let splits: Map<_, _> = iter.into_iter().map(|s| (s, true)).collect();
        let alphabet = CharAlphabet::from_iter(
            splits
                .keys()
                .flat_map(|Split(u, v, z)| u.iter().chain(v.iter()).chain(z.iter()))
                .cloned(),
        );
        Self { alphabet, splits }
    }
}

impl<A: WOFAlphabet> Incongruence<A> {
    /// ensures that the given split is contained. Returns `false` if needed to be added and `true` if it
    /// was already present.
    pub fn ensure_contains(
        &mut self,
        l: impl FiniteWord<A::Symbol>,
        r: impl FiniteWord<A::Symbol>,
        z: impl FiniteWord<A::Symbol>,
    ) -> bool {
        if self
            .splits
            .keys()
            .any(|Split(u, v, wit)| l.eq_deque(&u.0) && r.eq_deque(&v.0) && z.eq_deque(&wit.0))
        {
            return true;
        }

        self.add_split_raw(
            Split(
                Word(l.collect_deque()),
                Word(r.collect_deque()),
                Witness(z.collect_deque()),
            ),
            true,
        );
        false
    }

    pub fn refine(&mut self) -> bool {
        let mut changed = false;
        let mut i = 0;

        while i < self.splits.len() {
            let Some(entry) = self.splits.get_index_entry(i) else {
                panic!("Split index {i} is out of bounds here:\n{self:?}");
            };
            i += 1;

            println!("{entry:?}");

            if !*entry.get() {
                // this entry needs no refining
                continue;
            }

            let mut e = entry.key().clone();
            while e.refine() {
                changed = true;
                // we know this is refined as we are in the midst of refining its extension
                self.splits.insert(e.clone(), false);
            }

            self.splits.get_index_entry(i - 1).unwrap().insert(false);
        }

        changed
    }

    /// Returns true if the inserted split needs to be refined.
    pub fn add_split_raw(&mut self, split: Split<A::Symbol>, b: bool) -> Option<bool> {
        self.splits.insert(split, b)
    }

    /// Adds a split and ensures it is refined. Returns true this led to
    /// a change and false if no new information could be obtained from `split`.
    pub fn ensure_split(&mut self, split: Split<A::Symbol>) -> bool {
        if !self.splits.contains_key(&split) {
            self.add_split_raw(split, false)
                .expect("We know it's not there");
            assert!(self.refine(), "we know at least it needs to be refinable");
            true
        } else {
            false
        }
    }
}

impl<A: WOFAlphabet> Debug for Incongruence<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (Split(u, v, z), b) in &self.splits {
            writeln!(
                f,
                "({}, {}, {}), treated: {b}",
                u.as_string(),
                v.as_string(),
                z.as_string()
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn incongruence_splitting() {
        let mut incongruence = Incongruence::from_iter([("abb", "bb", "a")]);

        assert!(incongruence.refine());
        println!("SDLKFJSDF");
        assert!(!incongruence.refine());

        println!("incongruence: {incongruence:?}");

        assert!(incongruence.ensure_contains("a", "", "bba"));
        assert!(incongruence.ensure_contains("ab", "b", "ba"));
        assert_eq!(incongruence.splits.len(), 3);
    }
}
