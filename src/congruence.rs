mod class;

use crate::ts::EdgeOf;
use crate::ts::States;
use crate::{
    Void,
    alphabet::{Alphabet, CharAlphabet},
    word,
    word::OmegaWord,
};
pub use class::Class;
use std::collections::BTreeMap;

mod transitionprofile;
pub use transitionprofile::{Accumulates, RunProfile, RunSignature, TransitionMonoid};

mod cayley;
pub use cayley::{Cayley, RightCayley};

mod minimal_representative;
use crate::alphabet::Matcher;
use crate::automaton::DFA;
use crate::representation::IntoTs;
use crate::ts::operations::DefaultIfMissing;
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{
    Deterministic, EdgeExpression, EdgeTuple, ForAlphabet, IntoEdgeTuple, Shrinkable, Sproutable,
    StateColor, StateIndex, SymbolOf,
};
use crate::{DTS, Pointed, TransitionSystem};
pub use minimal_representative::{LazyMinimalRepresentatives, MinimalRepresentative, StateNaming};
use std::borrow::Cow;

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
    ///     upw, word::OmegaWord,
    ///     ts::Builder,
    ///     Congruence,
    /// };
    ///
    /// let ts = Builder::without_colors()
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
        let mut cur = self.reached_state(word.spoke())?;
        let mut count = 0;
        let mut map = BTreeMap::default();
        loop {
            match map.insert(cur, count) {
                None => {
                    count += 1;
                    cur = self.reached_state_from(cur, word.cycle())?;
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
/// transition system with a designated initial state. On top of the transition system `T`, it
/// lazily caches the minimal representatives of its classes, see
/// [`RightCongruence::minimal_representatives`].
///
/// The cache is discarded whenever the transition system is modified through one of the
/// [`Sproutable`] or [`Shrinkable`] methods. Mutating the system through [`Self::ts_mut`]
/// does not discard the cache, it is up to the caller to not change the structure then.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RightCongruence<T: TransitionSystem = DTS<CharAlphabet, Void, Void>> {
    ts: T,
    initial: T::StateIndex,
    minimal_representatives: LazyMinimalRepresentatives<T>,
}

impl<T: TransitionSystem> RightCongruence<T> {
    /// Creates a right congruence from a transition system and a designated initial state.
    pub fn from_parts(ts: T, initial: T::StateIndex) -> Self {
        Self {
            ts,
            initial,
            minimal_representatives: LazyMinimalRepresentatives::default(),
        }
    }

    /// Creates a right congruence from a pointed transition system.
    pub fn from_pointed(ts: T) -> Self
    where
        T: Pointed,
    {
        let initial = ts.initial();
        Self::from_parts(ts, initial)
    }

    /// Decomposes the congruence into the transition system and the initial state.
    pub fn into_parts(self) -> (T, StateIndex<T>) {
        (self.ts, self.initial)
    }

    /// Returns a reference to the underlying transition system.
    pub fn ts(&self) -> &T {
        &self.ts
    }

    /// Gives a mutable reference to the underlying transition system. The cached minimal
    /// representatives are not invalidated, so the transition structure should not be changed.
    pub fn ts_mut(&mut self) -> &mut T {
        &mut self.ts
    }

    /// Creates a right congruence over the given alphabet with a single state of the given
    /// color, which is the initial state.
    pub fn new_with_initial_color(alphabet: T::Alphabet, initial_color: T::StateColor) -> Self
    where
        T: ForAlphabet<T::Alphabet> + Sproutable,
    {
        let mut ts = T::for_alphabet(alphabet);
        let initial = ts.add_state(initial_color);
        Self::from_parts(ts, initial)
    }

    /// Like [`Self::new_with_initial_color`], but additionally adds a self-loop on the initial
    /// state for every symbol, each emitting the given edge color.
    pub fn new_trivial_with_initial_color(
        alphabet: T::Alphabet,
        initial_color: T::StateColor,
        edge_color: T::EdgeColor,
    ) -> Self
    where
        T: ForAlphabet<T::Alphabet> + Sproutable,
    {
        let alph = alphabet.clone();
        let mut out = Self::new_with_initial_color(alphabet, initial_color);
        let initial = out.initial;
        for sym in alph.universe() {
            out.ts.add_edge((
                initial,
                alph.make_expression(sym),
                edge_color.clone(),
                initial,
            ));
        }
        out
    }

    fn invalidate(&mut self) {
        self.minimal_representatives = LazyMinimalRepresentatives::default();
    }
}

impl<T: Congruence> From<T> for RightCongruence<T> {
    fn from(value: T) -> Self {
        Self::from_pointed(value)
    }
}

impl<T: Deterministic> Deterministic for RightCongruence<T> {
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        self.ts.edge(state, symbol)
    }
}

impl<T: TransitionSystem> Pointed for RightCongruence<T> {
    fn initial(&self) -> Self::StateIndex {
        self.initial
    }
}

impl<T: PredecessorIterable> PredecessorIterable for RightCongruence<T> {
    type EdgesToIter<'this>
        = T::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<T>) -> Option<Self::EdgesToIter<'_>> {
        self.ts.predecessors(state)
    }
}

impl<T: TransitionSystem> TransitionSystem for RightCongruence<T> {
    type Alphabet = T::Alphabet;

    type StateIndex = T::StateIndex;

    type StateColor = T::StateColor;

    type EdgeColor = T::EdgeColor;

    type EdgesFromIter<'this>
        = T::EdgesFromIter<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        self.ts.edges_from(state)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.ts.state_color(state)
    }

    fn state_bound(&self) -> Option<usize> {
        self.ts.state_bound()
    }
}

impl<T: States> States for RightCongruence<T> {
    type StatesIter<'this>
        = T::StatesIter<'this>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        self.ts.states()
    }

    fn state_count(&self) -> usize {
        self.ts.state_count()
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        self.ts.contains_state(index)
    }
}

impl<T: Sproutable> Sproutable for RightCongruence<T> {
    type Storage = T::Storage;

    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        self.invalidate();
        self.ts.add_state(color)
    }
    fn add_edge<E>(&mut self, t: E) -> crate::ts::EdgeId
    where
        E: IntoEdgeTuple<Self>,
    {
        self.invalidate();
        self.ts.add_edge(t.into_edge_tuple())
    }
    fn edge_color_mut(&mut self, id: crate::ts::EdgeId) -> Option<&mut crate::ts::EdgeColor<Self>> {
        self.invalidate();
        self.ts.edge_color_mut(id)
    }
    fn state_color_mut(&mut self, state: StateIndex<Self>) -> Option<&mut StateColor<Self>> {
        self.invalidate();
        self.ts.state_color_mut(state)
    }
}

impl<T: Shrinkable> Shrinkable for RightCongruence<T> {
    fn remove_edge(&mut self, id: crate::ts::EdgeId) -> Option<EdgeTuple<Self>> {
        self.invalidate();
        self.ts.remove_edge(id)
    }

    fn remove_state(&mut self, q: StateIndex<Self>) -> Option<Self::StateColor> {
        self.invalidate();
        self.ts.remove_state(q)
    }

    fn remove_edges_from_matching(
        &mut self,
        source: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<EdgeTuple<Self>>> {
        self.invalidate();
        self.ts.remove_edges_from_matching(source, matcher)
    }

    fn remove_edges_between_matching(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<EdgeTuple<Self>>> {
        self.invalidate();
        self.ts
            .remove_edges_between_matching(source, target, matcher)
    }

    fn remove_edges_between(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
    ) -> Option<Vec<EdgeTuple<Self>>> {
        self.invalidate();
        self.ts.remove_edges_between(source, target)
    }

    fn remove_edges_from(&mut self, source: StateIndex<Self>) -> Option<Vec<EdgeTuple<Self>>> {
        self.invalidate();
        self.ts.remove_edges_from(source)
    }

    fn remove_edges_to(&mut self, target: StateIndex<Self>) -> Option<Vec<EdgeTuple<Self>>> {
        self.invalidate();
        self.ts.remove_edges_to(target)
    }
}

impl<D: Deterministic> RightCongruence<D> {
    /// Checks if two finite words are congruent, meaning they reach the same state when
    /// starting from the initial state.
    pub fn congruent<W, V>(&self, word: W, other: V) -> bool
    where
        W: word::FiniteWord<Symbol = SymbolOf<D>>,
        V: word::FiniteWord<Symbol = SymbolOf<D>>,
    {
        self.reached_state(word).unwrap() == self.reached_state(other).unwrap()
    }

    /// Computes a DFA that accepts precisely those finite words which loop on the given `class`. Formally,
    /// if `u` represents the given class, then the DFA accepts precisely those words `w` such that `uw`
    /// is congruent to `u`.
    ///
    /// # Example
    /// ```
    /// use automata::ts::Builder;
    ///
    /// let ts = Builder::without_colors()
    ///     .with_transitions([(0, 'a', 1), (1, 'a', 0), (0, 'b', 0), (1, 'b', 1)])
    ///     .into_right_congruence(0);
    /// let dfa = ts.looping_words(1);
    /// assert!(dfa.accepts("aa"));
    /// assert!(!dfa.accepts("a"));
    /// assert!(dfa.accepts("b"));
    /// assert!(dfa.equivalent(ts.looping_words(0)));
    /// ```
    pub fn looping_words(&self, idx: StateIndex<Self>) -> DFA<DTS<D::Alphabet, bool, Void>>
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
        let out = &self.minimal_representatives;
        out.ensure_from(&self.ts, self.initial);
        out
    }

    /// Verifies whether an element of `self` is  idempotent, i.e. if the mr of the indexed
    /// class is u, then it should be that uu ~ u. Returns `None` if the class does not
    /// exist or is not labeled with a minimal representative.
    pub fn is_idempotent(&self, idx: StateIndex<Self>) -> Option<bool> {
        let mr = self.state_to_mr(idx)?;
        Some(self.reached_state_from(idx, mr) == Some(idx))
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
mod tests {
    use crate::ts::Builder;

    #[test]
    fn is_idempotent_is_none_for_unknown_classes() {
        let rc = Builder::without_colors()
            .with_transitions([(0, 'a', 1), (1, 'a', 0), (0, 'b', 0), (1, 'b', 1)])
            .into_right_congruence(0);
        assert!(rc.is_idempotent(0).is_some());
        assert_eq!(rc.is_idempotent(42), None);
    }
}
