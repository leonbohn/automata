use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
};

use itertools::Itertools;

use crate::alphabet::Symbol;

use super::{FiniteWord, OmegaWord, ReducedOmegaWord, Word};

/// Represents the normalization of an [`OmegaWord`] with regard to a transition system `T`. For an ultimately periodic word
/// `ux^ω`, we say that `T` is normalized if `u` and `ux` lead to the same state in `T`, which means that `x` loops on the state
/// that is reached after reading `u`.
///
/// For every transition system `T` and any ultimately periodic word `w = ux^ω`, there exists a unique minimal normalization of
/// `w` with regard to `T`. Moreover, this normalization can be efficiently computed in polynomial time.
///
/// # Example
/// Let `T` be a transition system that has two states (0 and 1), each of those has a self-loop on a symbol `b` and `a`-transitions lead
/// back and forth between the two states. Consider a word `w = ba^ω`, meaning `u = b` and `x = a`. Clearly `w` is not normalized wrt `T`
/// since `u` leads to `0` while `x` leads to `1`. The normalization of `w` wrt `T` would be `b(aa)^ω` since `aa` loops on the state `0`
/// that is reached after reading `b` from the initial state `0`.
#[derive(Clone, PartialEq, Eq)]
pub struct NormalizedOmegaWord<S: Symbol> {
    upw: ReducedOmegaWord<S>,
    pre_loop_count: usize,
    loop_size: usize,
    base: std::cell::OnceCell<Vec<S>>,
    rec: std::cell::OnceCell<Vec<S>>,
}

impl<S: Symbol> NormalizedOmegaWord<S> {
    /// Creates a new instance from the given ultimately periodic word `ux^ω`. The resulting normalized word will be
    /// `ux^i(x^j)^ω` where `i` is given by `pre_loop_count` and `j` is `loop_size`. This method should
    /// only really be called from inside the crate, for actually creating a normalization of an ultimately
    /// periodic word, there exist special functions in the `automata`
    /// package.
    ///
    /// # Example
    /// ```
    /// use automata_core::{upw, word::{OmegaWord, NormalizedOmegaWord}};
    ///
    /// let word = upw!("b", "a");
    /// let normalized = NormalizedOmegaWord::new(word, 1, 2);
    /// assert_eq!(normalized.spoke_vec(), vec!['b', 'a']);
    /// assert_eq!(normalized.cycle_vec(), vec!['a', 'a']);
    /// ```
    pub fn new(upw: ReducedOmegaWord<S>, pre_loop_count: usize, loop_size: usize) -> Self {
        assert!(loop_size > 0, "loop size must be positive");
        Self {
            upw,
            pre_loop_count,
            loop_size,
            base: std::cell::OnceCell::new(),
            rec: std::cell::OnceCell::new(),
        }
    }

    fn base_iter(&self) -> impl Iterator<Item = S> + '_ {
        self.upw.spoke().symbols().chain(
            self.upw
                .cycle()
                .symbols()
                .cycle()
                .take(self.upw.cycle_len() * self.pre_loop_count),
        )
    }

    fn rec_iter(&self) -> impl Iterator<Item = S> + '_ {
        self.upw
            .cycle()
            .symbols()
            .cycle()
            .take(self.upw.cycle_len() * self.loop_size)
    }
}

impl<S: Symbol> Word for NormalizedOmegaWord<S> {
    type Symbol = S;
    const FINITE: bool = false;
    fn nth(&self, position: usize) -> Option<S> {
        self.upw.nth(position)
    }
}

impl<S: Symbol> OmegaWord for NormalizedOmegaWord<S> {
    type Spoke<'this>
        = &'this [S]
    where
        Self: 'this;

    type Cycle<'this>
        = &'this [S]
    where
        Self: 'this;

    fn spoke(&self) -> Self::Spoke<'_> {
        self.base.get_or_init(|| self.base_iter().collect())
    }

    fn cycle(&self) -> Self::Cycle<'_> {
        self.rec.get_or_init(|| self.rec_iter().collect())
    }
}

impl<S: Symbol> Debug for NormalizedOmegaWord<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let base = self.base_iter().map(|s| s.show()).join("");
        let rec = self.rec_iter().map(|s| s.show()).join("");
        write!(f, "{base}·{rec}~{base}")
    }
}

impl<S: Symbol> Hash for NormalizedOmegaWord<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.upw.hash(state);
        self.pre_loop_count.hash(state);
        self.loop_size.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use crate::{upw, word::normalized::NormalizedOmegaWord};

    #[test]
    fn debug_normalized() {
        let upw = upw!("ab", "c");
        let nupw = NormalizedOmegaWord::new(upw, 1, 2);
        assert_eq!(format!("{:?}", nupw), "abc·cc~abc");
    }
}
