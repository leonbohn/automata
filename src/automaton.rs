use crate::ts::EdgeOf;
use crate::ts::SymbolOf;
mod acceptance_type;
use crate::ts::States;
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
/// acceptance condition `Sem`.
///
/// There are many different types of automata, which are obtained by choosing `Sem`
/// accordingly, see for example [`DFA`], [`MooreMachine`], [`DBA`] or [`DPA`]. Whether
/// the automaton reads finite or infinite words is not part of its type. Instead, it is
/// determined by the word type `W` for which `Sem` implements [`Semantics<T, W>`]: a
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
pub struct Automaton<T: TransitionSystem, Sem> {
    pub(crate) ts: T,
    initial: T::StateIndex,
    acceptance: Sem,
}

impl<Q: Color, C: Color + std::hash::Hash + Eq, Sem> Automaton<DTS<CharAlphabet, Q, C>, Sem> {
    /// Instantiates a new [`Builder`] for the edge and state color of `self`.
    pub fn builder() -> Builder<Q, C> {
        Builder::default()
    }
}

impl<T: TransitionSystem, Sem> Automaton<T, Sem> {
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
    ///     ts::{Sproutable, States, TransitionSystem},
    /// };
    ///
    /// let mut dfa: DFA = Automaton::new_with_initial_color(CharAlphabet::of_size(2), false);
    /// assert_eq!(dfa.state_count(), 1);
    /// dfa.add_edge((0, 'a', 0));
    /// dfa.add_edge((0, 'b', 0));
    /// assert!(!dfa.accepts("bbabababbabbba"));
    /// ```
    pub fn new_with_initial_color(alphabet: T::Alphabet, initial_color: T::StateColor) -> Self
    where
        T: ForAlphabet<T::Alphabet> + Sproutable,
        Sem: Default,
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
        Sem: Default,
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
    pub fn from_parts_with_acceptance(ts: T, initial: T::StateIndex, acceptance: Sem) -> Self {
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
        Sem: Default,
    {
        Self::from_parts_with_acceptance(ts, initial, Sem::default())
    }

    /// Builds a new instance of `Self` from a given congruence (transition system with designated
    /// initial state) as well as an acceptance condition.
    pub fn from_pointed_with_acceptance(cong: T, acceptance: Sem) -> Self
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
        Sem: Default,
    {
        let initial = cong.initial();
        Self::from_parts(cong, initial)
    }

    /// Decomposes the automaton into its parts: the transition system, the initial state and
    /// the acceptance condition.
    pub fn into_parts(self) -> (T, StateIndex<T>, Sem) {
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
    pub fn acceptance(&self) -> &Sem {
        &self.acceptance
    }
}

impl<T: Deterministic, Sem> Automaton<T, Sem> {
    /// Returns whether the automaton accepts the given word. The word can be finite or
    /// infinite, depending on which of the two the acceptance condition `Sem` supports.
    pub fn accepts<W>(&self, word: W) -> bool
    where
        Sem: Semantics<T, W, Output = bool>,
    {
        self.transform(word).unwrap_or(false)
    }

    /// Transforms the given word using the automaton, that means it returns the output of
    /// the acceptance condition on the run of the word, or `None` if the run is not
    /// defined because it leaves the transition system.
    pub fn transform<W>(&self, word: W) -> Option<Sem::Output>
    where
        Sem: Semantics<T, W>,
    {
        let observed = self.acceptance.observe(&self.ts, self.initial, word)?;
        Some(self.acceptance.evaluate(observed))
    }
}

impl<T: TransitionSystem, Sem> AsRef<Automaton<T, Sem>> for Automaton<T, Sem> {
    fn as_ref(&self) -> &Automaton<T, Sem> {
        self
    }
}

impl<T: Deterministic, Sem> Deterministic for Automaton<T, Sem> {
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        self.ts.edge(state, symbol)
    }
}

impl<T: PredecessorIterable, Sem> PredecessorIterable for Automaton<T, Sem> {
    type EdgesToIter<'this>
        = T::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<T>) -> Option<Self::EdgesToIter<'_>> {
        self.ts.predecessors(state)
    }
}

impl<T: TransitionSystem, Sem> Pointed for Automaton<T, Sem> {
    fn initial(&self) -> Self::StateIndex {
        self.initial
    }
}

impl<T: Sproutable, Sem> Sproutable for Automaton<T, Sem> {
    type Storage = T::Storage;

    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        self.ts.add_state(color)
    }
    fn add_edge<E>(&mut self, t: E) -> crate::ts::EdgeId
    where
        E: IntoEdgeTuple<Self>,
    {
        self.ts.add_edge(t.into_edge_tuple())
    }
    fn edge_color_mut(&mut self, id: crate::ts::EdgeId) -> Option<&mut crate::ts::EdgeColor<Self>> {
        self.ts.edge_color_mut(id)
    }
    fn state_color_mut(&mut self, state: StateIndex<Self>) -> Option<&mut StateColor<Self>> {
        self.ts.state_color_mut(state)
    }
}

impl<T: Shrinkable, Sem> Shrinkable for Automaton<T, Sem> {
    fn remove_edge(&mut self, id: crate::ts::EdgeId) -> Option<crate::ts::EdgeTuple<Self>> {
        self.ts.remove_edge(id)
    }

    fn out_edge_ids(
        &self,
        source: StateIndex<Self>,
        keep: impl for<'e> FnMut(&crate::ts::EdgeOf<'e, Self>) -> bool,
    ) -> Option<Vec<crate::ts::EdgeId>> {
        self.ts.out_edge_ids(source, keep)
    }

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

impl<T: TransitionSystem, Sem> TransitionSystem for Automaton<T, Sem> {
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

impl<T: States, Sem> States for Automaton<T, Sem> {
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

impl<T: TransitionSystem + std::fmt::Debug, Sem: std::fmt::Debug> std::fmt::Debug
    for Automaton<T, Sem>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}\n{:?}", self.acceptance, self.ts)
    }
}

/// Iterator over the accepting states of a [`TransitionSystem`] that have a certain coloring.
pub struct StatesWithColor<'a, Ts: States> {
    ts: &'a Ts,
    iter: Ts::StatesIter<'a>,
    color: Ts::StateColor,
}

impl<'a, Ts: States> StatesWithColor<'a, Ts> {
    /// Creates a new instance for the given transition system and color.
    pub fn new(ts: &'a Ts, color: Ts::StateColor) -> Self {
        Self {
            iter: ts.states(),
            ts,
            color,
        }
    }
}

impl<Ts: States> Clone for StatesWithColor<'_, Ts> {
    fn clone(&self) -> Self {
        Self {
            ts: self.ts,
            iter: self.ts.states(),
            color: self.color.clone(),
        }
    }
}

impl<Ts: States<StateColor = bool>> Iterator for StatesWithColor<'_, Ts> {
    type Item = Ts::StateIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .find(|&index| *self.ts.state_color(index).unwrap() == self.color)
    }
}

impl<T: Congruence, Sem: Default> From<T> for Automaton<T, Sem> {
    fn from(value: T) -> Self {
        let initial = value.initial();
        Self::from_parts(value, initial)
    }
}

impl<T: Deterministic, Sem: Default> From<(T, StateIndex<T>)> for Automaton<T, Sem> {
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
