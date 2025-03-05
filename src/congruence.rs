mod class;

use crate::core::{
    Color, Void,
    alphabet::{Alphabet, CharAlphabet},
    math, word,
    word::OmegaWord,
};
pub use class::Class;

mod transitionprofile;
pub use transitionprofile::{Accumulates, RunProfile, RunSignature, TransitionMonoid};

mod cayley;
pub use cayley::{Cayley, RightCayley};

mod minimal_representative;
use crate::automaton::{DFA, FiniteWordAutomaton};
use crate::representation::IntoTs;
use crate::ts::operations::DefaultIfMissing;
use crate::ts::{Deterministic, EdgeColor, StateColor, StateIndex, SymbolOf};
use crate::{DTS, Pointed, TransitionSystem};
pub use minimal_representative::{LazyMinimalRepresentatives, MinimalRepresentative, StateNaming};

/// A congruence is a [`TransitionSystem`], which additionally has a distinguished initial state. On top
/// of that, a congruence does not have any coloring on either states or symbols. This
/// functionality is abstracted in [`Pointed`]. This trait is automatically implemented.
pub trait Congruence: Deterministic + Pointed {
    /// Computes the normalization with regard to the given deterministic transition system `cong`.
    /// Specifically, for an ultimately periodic word `ux^ω`, this procedure returns the ultimately
    /// periodic word `u^i(x^j)^ω` such that `i` and `j` are the least natural numbers verifying that
    /// `u^i` and `u^ix^j` lead the same state in `cong`.
    ///
    /// The function will return `None` if no normalization exists. This may be the case if the
    /// transition system is incomplete.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     core::{upw, word::OmegaWord},
    ///     ts::TSBuilder,
    ///     Congruence,
    /// };
    ///
    /// let ts = TSBuilder::without_colors()
    ///     .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (1, 'b', 1)])
    ///     .into_dts_with_initial(0);
    /// let word = upw!("b", "a");
    /// let normalized = ts.normalize_upw(&word).expect("must be normalizable");
    /// assert_eq!(normalized.spoke_vec(), vec!['b']);
    /// assert_eq!(normalized.cycle_vec(), vec!['a', 'a']);
    /// ```
    fn normalize_upw(
        &self,
        word: impl OmegaWord<Symbol = SymbolOf<Self>>,
    ) -> Option<word::NormalizedOmegaWord<SymbolOf<Self>>>
    where
        Self: Pointed,
    {
        let mut cur = self.reached_state_index(word.spoke())?;
        let mut count = 0;
        let mut map = math::OrderedMap::default();
        loop {
            match map.insert(cur, count) {
                None => {
                    count += 1;
                    cur = self.reached_state_index_from(cur, word.cycle())?;
                }
                Some(i) => {
                    // the spoke is the spoke of self plus `i` times the cycle, while the
                    // cycle is `count - i` times the cycle
                    assert!(i < count);
                    return Some(word::NormalizedOmegaWord::new(word.reduced(), i, count - i));
                }
            }
        }
    }
}
impl<C: Deterministic + Pointed> Congruence for C {}

/// Represents a right congruence relation, which is in essence a trim, deterministic
/// transition system with a designated initial state.
pub type RightCongruence<A = CharAlphabet, Q = Void, C = Void, D = DTS<A, Q, C>> =
    FiniteWordAutomaton<A, LazyMinimalRepresentatives<D>, Q, C, true, D>;

/// Type alias for a [`RightCongruence`] that is obtained by wrapping the given transition system.
pub type IntoRightCongruence<D> =
    RightCongruence<<D as TransitionSystem>::Alphabet, StateColor<D>, EdgeColor<D>, D>;

/// Type alias for a [`RightCongruence`] that is by collecting the given transition system.
pub type CollectRightCongruence<D> =
    RightCongruence<<D as TransitionSystem>::Alphabet, StateColor<D>, EdgeColor<D>>;

impl<A: Alphabet, Q: Color, C: Color, D> RightCongruence<A, Q, C, D>
where
    D: Deterministic<Alphabet = A, StateColor = Q, EdgeColor = C>,
{
    /// Computes a DFA that accepts precisely those finite words which loop on the given `class`. Formally,
    /// if `u` represents the given class, then the DFA accepts precisely those words `w` such that `uw`
    /// is congruent to `u`.
    ///
    /// # Example
    /// ```
    /// use automata::ts::TSBuilder;
    ///
    /// let ts = TSBuilder::without_colors()
    ///     .with_transitions([(0, 'a', 1), (1, 'a', 0), (0, 'b', 0), (1, 'b', 1)])
    ///     .into_right_congruence_bare(0);
    /// let dfa = ts.looping_words(1);
    /// assert!(dfa.accepts("aa"));
    /// assert!(!dfa.accepts("a"));
    /// assert!(dfa.accepts("b"));
    /// assert!(dfa.equivalent(ts.looping_words(0)));
    /// ```
    pub fn looping_words(&self, idx: StateIndex<Self>) -> DFA<A>
    where
        D: Clone + IntoTs,
    {
        self.ts()
            .clone()
            .with_initial(idx)
            .with_state_color(DefaultIfMissing::new(
                [(idx, true)].into_iter().collect(),
                false,
            ))
            .into_dfa()
    }

    /// Returns a reference to the minimal representatives of the classes of the right congruence.
    pub fn minimal_representatives(&self) -> &LazyMinimalRepresentatives<D> {
        let out = self.acceptance();
        out.ensure_from(self.ts(), self.initial());
        out
    }

    /// Verifies whether an element of `self` is  idempotent, i.e. if the mr of the indexed
    /// class is u, then it should be that uu ~ u.
    pub fn is_idempotent(&self, idx: StateIndex<Self>) -> bool {
        let Some(mr) = self.state_to_mr(idx) else {
            panic!("The class {idx:?} is not labeled!");
        };
        self.reached_state_index_from(idx, mr) == Some(idx)
    }

    /// Returns the [`Class`] that is referenced by `index`.
    #[inline(always)]
    pub fn state_to_mr(&self, idx: StateIndex<Self>) -> Option<&MinimalRepresentative<D>> {
        self.minimal_representatives().get_by_left(&idx)
    }

    #[inline(always)]
    /// Returns the index of the class containing the given word.
    pub fn mr_to_state(&self, class: &MinimalRepresentative<D>) -> Option<StateIndex<Self>> {
        self.minimal_representatives().get_by_right(class).cloned()
    }

    /// Returns an iterator which yields pairs `(c, idx)` consisting of a reference `c` to the class name together
    /// with the corresponding index of the class.
    pub fn classes(
        &self,
    ) -> impl Iterator<Item = (&MinimalRepresentative<D>, StateIndex<Self>)> + '_ {
        self.minimal_representatives()
            .iter()
            .map(|(idx, mr)| (mr, *idx))
    }
}

#[cfg(test)]
mod tests {}
