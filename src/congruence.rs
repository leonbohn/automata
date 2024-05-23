use crate::prelude::*;

mod class;
pub use class::Class;

mod forc;
pub use forc::FORC;

mod transitionprofile;
pub use transitionprofile::{Accumulates, RunProfile, RunSignature, TransitionMonoid};

mod cayley;
pub use cayley::{Cayley, RightCayley};

mod minimal_representative;
pub use minimal_representative::{LazyMinimalRepresentatives, MinimalRepresentative};

/// A congruence is a [`TransitionSystem`], which additionally has a distinguished initial state. On top
/// of that, a congruence does not have any coloring on either states or symbols. This
/// functionality is abstracted in [`Pointed`]. This trait is automatically implemented.
pub trait Congruence: Deterministic + Pointed {
    /// Takes ownership of `self` and builds a new [`DFA`] from it.
    fn into_dfa(self) -> IntoDFA<Self>
    where
        Self: Congruence<StateColor = bool>,
    {
        Automaton::from_pointed(self)
    }

    /// Collects the transition system representing `self` and builds a new [`DFA`].
    fn collect_dfa(&self) -> DFA<Self::Alphabet>
    where
        Self: Congruence<StateColor = bool>,
    {
        let (dts, initial) = self.erase_edge_colors().collect_dts();
        DFA::from_parts(dts, initial)
    }

    /// Takes ownership of `self` and builds a new [`DPA`] from it.
    fn into_dpa(self) -> IntoDPA<Self>
    where
        Self: Congruence<EdgeColor = Int>,
    {
        Automaton::from_pointed(self)
    }

    /// Collects the transition system representing `self` and builds a new [`DPA`].
    fn collect_dpa(&self) -> DPA<Self::Alphabet>
    where
        Self: Congruence<EdgeColor = Int>,
    {
        let (ts, initial) = self.erase_state_colors().collect_dts_pointed();
        DPA::from_parts(ts, initial)
    }

    /// Takes ownership of `self` and builds a new [`DBA`] from it.
    fn into_dba(self) -> IntoDBA<Self>
    where
        Self: Congruence<EdgeColor = bool>,
    {
        Automaton::from_pointed(self)
    }

    /// Collects the transition system representing `self` and builds a new [`DBA`].
    fn collect_dba(&self) -> DBA<Self::Alphabet>
    where
        Self: Congruence<EdgeColor = bool>,
    {
        let (ts, initial) = self.erase_state_colors().collect_dts_pointed();
        DBA::from_parts(ts, initial)
    }

    /// Takes ownership of `self` and builds a new [`MooreMachine`] from it.
    fn into_moore(self) -> IntoMooreMachine<Self>
    where
        StateColor<Self>: Color,
    {
        Automaton::from_pointed(self)
    }

    /// Collects the transition system representing `self` and builds a new [`MooreMachine`].
    fn collect_moore(&self) -> MooreMachine<Self::Alphabet, StateColor<Self>>
    where
        StateColor<Self>: Color,
    {
        let (ts, initial) = self.erase_edge_colors().collect_dts_pointed();
        MooreMachine::from_parts(ts, initial)
    }

    /// Collects the transition system representing `self` and builds a new [`MealyMachine`].
    fn into_mealy(self) -> IntoMealyMachine<Self>
    where
        EdgeColor<Self>: Color,
    {
        Automaton::from_pointed(self)
    }
    /// Collects the transition system representing `self` and builds a new [`MealyMachine`].
    fn collect_mealy(&self) -> MealyMachine<Self::Alphabet, StateColor<Self>, EdgeColor<Self>>
    where
        EdgeColor<Self>: Color,
    {
        let (ts, initial) = self.collect_dts_pointed();
        MealyMachine::from_parts(ts, initial)
    }

    /// Creates a new instance of a [`RightCongruence`] from the transition structure of `self`.
    /// Note, that this method might not preserve state indices!
    fn into_right_congruence(self) -> IntoRightCongruence<Self>
    where
        Self: Pointed,
    {
        RightCongruence::from_pointed(self)
    }

    /// Creates a new instance of a [`RightCongruence`] from the transition structure of `self`.
    /// Note, that this method might not preserve state indices!
    fn collect_right_congruence(self) -> CollectRightCongruence<Self>
    where
        Self: Pointed,
    {
        let (ts, initial) = self.collect_dts_pointed();
        RightCongruence::from_parts(ts, initial)
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
    /// use automata::prelude::*;
    ///
    /// let ts = TSBuilder::without_colors()
    ///     .with_transitions([(0, 'a', 1), (1, 'a', 0), (0, 'b', 0), (1, 'b', 1)])
    ///     .into_right_congruence_bare(0);
    ///
    /// let dfa = ts.looping_words(1);
    /// assert!(dfa.accepts("aa"));
    /// assert!(!dfa.accepts("a"));
    /// assert!(dfa.accepts("b"));
    ///
    /// assert!(dfa.equivalent(ts.looping_words(0)));
    /// ```
    pub fn looping_words<Idx: Indexes<Self>>(&self, class: Idx) -> DFA<A> {
        let idx = class.to_index(self).unwrap();
        self.ts()
            .with_initial(idx)
            .with_state_color(DefaultIfMissing::new(
                [(idx, true)].into_iter().collect(),
                false,
            ))
            .collect_dfa()
    }

    /// Returns a reference to the minimal representatives of the classes of the right congruence.
    pub fn minimal_representatives(&self) -> &LazyMinimalRepresentatives<A, StateIndex<D>> {
        self.acceptance()
    }

    /// Verifies whether an element of `self` is  idempotent, i.e. if the mr of the indexed
    /// class is u, then it should be that uu ~ u.
    pub fn is_idempotent<I: Indexes<Self>>(&self, elem: I) -> bool {
        let Some(idx) = elem.to_index(self) else {
            panic!("is_idempotent called for non-existent index");
        };
        let Some(mr) = self.state_to_mr(idx) else {
            panic!("The class {} is not labeled!", idx.show());
        };
        if let Some(q) = self.get(elem) {
            self.reached_state_index_from(q, mr) == Some(q)
        } else {
            false
        }
    }

    /// Returns the [`Class`] that is referenced by `index`.
    #[inline(always)]
    pub fn state_to_mr<Idx: Indexes<Self>>(
        &self,
        index: Idx,
    ) -> Option<&MinimalRepresentative<A::Symbol>> {
        let idx = index.to_index(self)?;
        self.minimal_representatives().get_by_left(&idx)
    }

    #[inline(always)]
    /// Returns the index of the class containing the given word.
    pub fn mr_to_state(
        &self,
        class: &MinimalRepresentative<A::Symbol>,
    ) -> Option<StateIndex<Self>> {
        self.minimal_representatives().get_by_right(class).cloned()
    }

    /// Returns an iterator which yields pairs `(c, idx)` consisting of a reference `c` to the class name together
    /// with the corresponding index of the class.
    pub fn classes(
        &self,
    ) -> impl Iterator<Item = (&MinimalRepresentative<A::Symbol>, StateIndex<Self>)> + '_ {
        self.minimal_representatives()
            .iter()
            .map(|(idx, mr)| (mr, *idx))
    }
}
