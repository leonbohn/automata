mod acceptance_type;
use crate::{
    Color,
    alphabet::{Alphabet, CharAlphabet, Matcher},
};
pub use acceptance_type::OmegaAcceptanceType;
use std::borrow::Cow;

#[macro_use]
mod moore;
pub use moore::{MooreMachine, MooreSemantics};

#[macro_use]
mod mealy;
pub use mealy::{MealyLike, MealyMachine, MealySemantics};

mod reachability;
pub use reachability::{DFA, ReachabilityCondition};

mod omega;
pub use omega::{
    AcceptanceError, AcceptanceMask, BuchiCondition, DBA, DMA, DPA, DRA,
    DeterministicOmegaAutomaton, MaxEvenParityCondition, MaxOddParityCondition,
    MinEvenParityCondition, MinOddParityCondition, MullerCondition, NondeterministicOmegaAutomaton,
    OmegaAcceptanceCondition, OmegaAutomaton, RabinCondition, RabinPair,
};

mod with_initial;
pub use with_initial::{WithInitial, WithoutCondition};

/// Defines the semantics of automata, i.e. when something is accepted.
pub mod semantics;
pub use semantics::Semantics;

mod deterministic;

mod priority_mapping;
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{
    Builder, Deterministic, EdgeExpression, ForAlphabet, IntoEdgeTuple, Shrinkable, Sproutable,
    StateColor, StateIndex,
};
use crate::{Congruence, DTS, Pointed, TransitionSystem};
pub use priority_mapping::{StateBasedWeakPriorityMapping, WeakPriorityMapping};

/// An automaton consists of a transition system `T`, a designated initial state and an
/// acceptance condition `Z`.
///
/// There are many different types of automata, which are obtained by choosing `Z`
/// accordingly, see for example [`DFA`], [`MooreMachine`], [`DBA`] or [`DPA`]. Whether
/// the automaton reads finite or infinite words is not part of its type. Instead, it is
/// determined by the word type `W` for which `Z` implements [`Semantics<T, W>`]: a
/// [`ReachabilityCondition`] evaluates finite words, a [`BuchiCondition`] infinite ones.
/// A single [`Automaton::accepts`] then serves both cases, `W` is inferred from the argument.
///
/// ```
/// use automata::{automaton::{DBA, DFA}, ts::Builder, upw};
///
/// let dfa = DFA::builder()
///     .with_state_colors([true, false])
///     .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 0)])
///     .into_dfa(0);
/// assert!(dfa.accepts("ab"));
///
/// let dba = DBA::builder()
///     .with_edges([(0, 'a', true, 0), (0, 'b', false, 0)])
///     .into_dba(0);
/// assert!(dba.accepts(upw!("a")));
/// ```
#[derive(Clone, Eq, PartialEq)]
pub struct Automaton<T: TransitionSystem, Z> {
    pub(crate) ts: T,
    initial: T::StateIndex,
    acceptance: Z,
}

impl<Q: Color, C: Color + std::hash::Hash + Eq, Z> Automaton<DTS<CharAlphabet, Q, C>, Z> {
    /// Instantiates a new [`Builder`] for the edge and state color of `self`.
    pub fn builder() -> Builder<Q, C> {
        Builder::default()
    }
}

impl<T: TransitionSystem, Z> Automaton<T, Z> {
    /// Creates a new instance of `Self` for the given [`Alphabet`]. Also
    /// takes the colour of the initial state as parameter as this method
    /// simply creates a new transition system and adds a state with the
    /// given color.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     automaton::{Automaton, DFA},
    ///     alphabet::CharAlphabet,
    ///     ts::{Sproutable, TransitionSystem},
    /// };
    ///
    /// let mut dfa: DFA = Automaton::new_with_initial_color(CharAlphabet::of_size(2), false);
    /// assert_eq!(dfa.size(), 1);
    /// dfa.add_edge((0, 'a', 0));
    /// dfa.add_edge((0, 'b', 0));
    /// assert!(!dfa.accepts("bbabababbabbba"));
    /// ```
    pub fn new_with_initial_color(alphabet: T::Alphabet, initial_color: T::StateColor) -> Self
    where
        T: ForAlphabet<T::Alphabet> + Sproutable,
        Z: Default,
    {
        let mut ts = T::for_alphabet(alphabet);
        let initial = ts.add_state(initial_color);
        Self::from_parts(ts, initial)
    }

    /// Uses `Self::new_with_initial_color` to create a new instance of
    /// `Self` and then makes all transitions self-loops emitting the given
    /// color.
    pub fn new_trivial_with_initial_color(
        alphabet: T::Alphabet,
        initial_color: T::StateColor,
        edge_color: T::EdgeColor,
    ) -> Self
    where
        T: ForAlphabet<T::Alphabet> + Sproutable,
        Z: Default,
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

    /// Creates a new automaton from the given transition system and acceptance condition.
    pub fn from_parts_with_acceptance(ts: T, initial: T::StateIndex, acceptance: Z) -> Self {
        Self {
            initial,
            ts,
            acceptance,
        }
    }

    /// Builds a new instance of `Self` from the given parts, that is a transition system `ts` and
    /// a designated `initial` state. Assumes the acceptance type implements `Default`.
    pub fn from_parts(ts: T, initial: T::StateIndex) -> Self
    where
        Z: Default,
    {
        Self::from_parts_with_acceptance(ts, initial, Z::default())
    }

    /// Builds a new instance of `Self` from a given congruence (transition system with designated
    /// initial state) as well as an acceptance condition.
    pub fn from_pointed_with_acceptance(cong: T, acceptance: Z) -> Self
    where
        T: Pointed,
    {
        let initial = cong.initial();
        Self::from_parts_with_acceptance(cong, initial, acceptance)
    }

    /// Builds an instance of `Self` from a pointed transition system. Assumes the acceptance type implements `Default`.
    pub fn from_pointed(cong: T) -> Self
    where
        T: Pointed,
        Z: Default,
    {
        let initial = cong.initial();
        Self::from_parts(cong, initial)
    }

    /// Decomposes the automaton into its parts: the transition system, the initial state and
    /// the acceptance condition.
    pub fn into_parts(self) -> (T, StateIndex<T>, Z) {
        (self.ts, self.initial, self.acceptance)
    }

    /// Returns a reference to the underlying transition system.
    pub fn ts(&self) -> &T {
        &self.ts
    }

    /// Gives a mutable reference to the underlying transition system.
    pub fn ts_mut(&mut self) -> &mut T {
        &mut self.ts
    }

    /// Returns a reference to the acceptance condition.
    pub fn acceptance(&self) -> &Z {
        &self.acceptance
    }
}

impl<T: Deterministic, Z> Automaton<T, Z> {
    /// Returns whether the automaton accepts the given word. The word can be finite or
    /// infinite, depending on which of the two the acceptance condition `Z` supports.
    pub fn accepts<W>(&self, word: W) -> bool
    where
        Z: Semantics<T, W, Output = bool>,
    {
        self.transform(word).unwrap_or(false)
    }

    /// Transforms the given word using the automaton, that means it returns the output of
    /// the acceptance condition on the run of the word, or `None` if the run is not
    /// defined because it leaves the transition system.
    pub fn transform<W>(&self, word: W) -> Option<Z::Output>
    where
        Z: Semantics<T, W>,
    {
        let observed = self.acceptance.observe(&self.ts, self.initial, word)?;
        Some(self.acceptance.evaluate(observed))
    }
}

impl<T: TransitionSystem, Z> AsRef<Automaton<T, Z>> for Automaton<T, Z> {
    fn as_ref(&self) -> &Automaton<T, Z> {
        self
    }
}

impl<T: Deterministic, Z> Deterministic for Automaton<T, Z> {}

impl<T: PredecessorIterable, Z> PredecessorIterable for Automaton<T, Z> {
    type PreEdgeRef<'this>
        = T::PreEdgeRef<'this>
    where
        Self: 'this;

    type EdgesToIter<'this>
        = T::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<T>) -> Option<Self::EdgesToIter<'_>> {
        self.ts.predecessors(state)
    }
}

impl<T: TransitionSystem, Z> Pointed for Automaton<T, Z> {
    fn initial(&self) -> Self::StateIndex {
        self.initial
    }
}

impl<T: Sproutable, Z> Sproutable for Automaton<T, Z> {
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        self.ts.add_state(color)
    }
    fn set_state_color(&mut self, index: StateIndex<Self>, color: StateColor<Self>) {
        self.ts.set_state_color(index, color)
    }
    fn add_edge<E>(&mut self, t: E) -> Option<crate::ts::EdgeTuple<Self>>
    where
        E: IntoEdgeTuple<Self>,
    {
        self.ts.add_edge(t.into_edge_tuple())
    }
}

impl<T: Shrinkable, Z> Shrinkable for Automaton<T, Z> {
    fn remove_state(&mut self, q: StateIndex<Self>) -> Option<Self::StateColor> {
        self.ts.remove_state(q)
    }

    fn remove_edges_from_matching(
        &mut self,
        source: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts.remove_edges_from_matching(source, matcher)
    }

    fn remove_edges_between_matching(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts
            .remove_edges_between_matching(source, target, matcher)
    }

    fn remove_edges_between(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts.remove_edges_between(source, target)
    }

    fn remove_edges_from(
        &mut self,
        source: StateIndex<Self>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts.remove_edges_from(source)
    }

    fn remove_edges_to(
        &mut self,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts.remove_edges_to(target)
    }
}

impl<T: TransitionSystem, Z> TransitionSystem for Automaton<T, Z> {
    type Alphabet = T::Alphabet;

    type StateIndex = T::StateIndex;

    type StateColor = T::StateColor;

    type EdgeColor = T::EdgeColor;

    type EdgeRef<'this>
        = T::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = T::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this>
        = T::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_bound(&self) -> Option<usize> {
        self.ts.state_bound()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.ts.state_indices()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        self.ts.edges_from(state)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.ts.state_color(state)
    }

    fn contains_state_index(&self, index: StateIndex<Self>) -> bool {
        self.ts.contains_state_index(index)
    }
}

impl<T: TransitionSystem + std::fmt::Debug, Z: std::fmt::Debug> std::fmt::Debug
    for Automaton<T, Z>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}\n{:?}", self.acceptance, self.ts)
    }
}

/// Iterator over the accepting states of a [`TransitionSystem`] that have a certain coloring.
pub struct StatesWithColor<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    iter: Ts::StateIndices<'a>,
    color: Ts::StateColor,
}

impl<'a, Ts: TransitionSystem> StatesWithColor<'a, Ts> {
    /// Creates a new instance for the given transition system and color.
    pub fn new(ts: &'a Ts, color: Ts::StateColor) -> Self {
        Self {
            iter: ts.state_indices(),
            ts,
            color,
        }
    }
}

impl<Ts: TransitionSystem> Clone for StatesWithColor<'_, Ts> {
    fn clone(&self) -> Self {
        Self {
            ts: self.ts,
            iter: self.ts.state_indices(),
            color: self.color.clone(),
        }
    }
}

impl<Ts: TransitionSystem<StateColor = bool>> Iterator for StatesWithColor<'_, Ts> {
    type Item = Ts::StateIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .find(|&index| *self.ts.state_color(index).unwrap() == self.color)
    }
}

impl<T: Congruence, Z: Default> From<T> for Automaton<T, Z> {
    fn from(value: T) -> Self {
        let initial = value.initial();
        Self::from_parts(value, initial)
    }
}

impl<T: Deterministic, Z: Default> From<(T, StateIndex<T>)> for Automaton<T, Z> {
    fn from((ts, initial): (T, StateIndex<T>)) -> Self {
        Self::from_parts(ts, initial)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn set_initial_color_on_automaton() {
        use crate::alphabet::CharAlphabet;
        use crate::ts::Sproutable;
        use crate::{Pointed, TransitionSystem};

        let mut dfa: DFA =
            super::Automaton::new_with_initial_color(CharAlphabet::of_size(2), false);
        assert_eq!(dfa.state_color(dfa.initial()).as_deref(), Some(&false));
        dfa.set_initial_color(true);
        assert_eq!(dfa.state_color(dfa.initial()).as_deref(), Some(&true));
    }

    use crate::automaton::{DBA, DFA, MooreMachine};
    use crate::representation::CollectTs;
    use crate::word::ReducedOmegaWord;

    #[test]
    fn mealy_color_or_below() {
        let mm = MooreMachine::builder()
            .with_state_colors([0, 1, 1, 0])
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 2),
                (1, 'a', 2),
                (1, 'b', 2),
                (2, 'a', 3),
                (2, 'b', 3),
                (3, 'a', 3),
                (3, 'b', 3),
            ])
            .into_moore(0);

        let dfas = mm.decompose_dfa();
        let dfa1 = &dfas[1];
        let dfa0 = &dfas[0];

        assert!(dfa1.accepts(""));
        assert!(dfa1.accepts("b"));
        assert!(!dfa0.accepts("b"));
        assert!(dfa0.accepts("ba"));
    }

    #[test]
    fn dbas() {
        let dba = DBA::builder()
            .with_edges([
                (0, 'a', true, 1),
                (0, 'b', false, 0),
                (1, 'a', true, 1),
                (1, 'b', false, 0),
            ])
            .into_dba(0);
        assert!(dba.accepts(ReducedOmegaWord::periodic("abb")));
        assert!(!dba.accepts(ReducedOmegaWord::periodic("b")));
        assert!(dba.accepts(upw!("a")));
        assert!(!dba.accepts(upw!("b")));

        assert!(!dba.is_empty());
    }

    #[test]
    fn dfas_and_boolean_operations() {
        let dfa = DFA::builder()
            .with_state_colors([true, false])
            .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 0)])
            .into_dfa(0);

        assert!(!dfa.is_empty_language());
        assert_eq!(dfa.give_word(), Some(vec![]));

        let _dfb = dfa.clone();

        assert!(dfa.accepts("ababab"));
        assert!(!dfa.accepts("a"));

        let notdfa = dfa.as_ref().negation().collect_dfa();
        assert!(!notdfa.accepts("ababab"));
        assert!(notdfa.accepts("a"));

        let intersection = dfa.as_ref().intersection(&notdfa).collect_dfa();
        assert!(!intersection.accepts("ababab"));
        assert!(!intersection.accepts("a"));

        let union = dfa.as_ref().union(&notdfa).collect_dfa();
        assert!(union.accepts("ababab"));
        assert!(union.accepts("a"));
    }
}
