use crate::{
    Color,
    alphabet::Symbol,
    math,
    word::Infix,
    word::{FiniteWord, OmegaWord, ReducedOmegaWord, Word},
};
use std::collections::BTreeSet;
use std::{fmt::Debug, marker::PhantomData};

use crate::TransitionSystem;
use crate::ts::{Deterministic, EdgeColor, IdType, StateColor, StateIndex, SymbolOf};

/// Observes a run on a [`TransitionSystem`] and collects information about it, for example the
/// state that is reached or the colors that are seen. A run feeds the symbols of a word one by
/// one to the observer, which can also decide to stop the run.
pub trait Observer<T: TransitionSystem>: Sized {
    /// The information that the observer has collected so far.
    type Current;
    /// Returns the information collected so far.
    fn current(&self) -> &Self::Current;
    /// Consumes the observer and returns the collected information.
    fn into_current(self) -> Self::Current;
    /// Creates an observer for a run that starts in `state`.
    fn begin(ts: &T, state: StateIndex<T>) -> Self;
    /// Observes a transition on `sym` taken from `state` and returns the state that is reached, or
    /// `None` if there is no such transition (the run escapes the transition system).
    fn observe_one(
        &mut self,
        ts: &T,
        state: StateIndex<T>,
        sym: SymbolOf<T>,
    ) -> Option<StateIndex<T>>;
}

/// An [`Observer`] that can also summarize an infinite run, which ends up in a cycle.
pub trait InfiniteObserver<T: TransitionSystem>: Observer<T> {
    /// Summarizes the infinite run from the observations `seq` of the iterations of the loop; the
    /// run enters the cycle (the part that repeats forever) at iteration `time`.
    fn loop_back(seq: &[Self::Current], ts: &T, time: usize) -> Self::Current;
}

/// Observes nothing, only the success of the run matters.
#[derive(Debug, Clone, Copy)]
pub struct NoObserver;
/// Observes the state that is reached.
#[derive(Debug, Clone, Copy)]
pub struct ReachedState<Idx>(Idx);
/// Observes the color of the last edge that was taken.
#[derive(Debug, Clone)]
pub struct ReachedEdgeColor<T: TransitionSystem>(Option<EdgeColor<T>>);
/// Observes the color of the state that is reached.
#[derive(Debug, Clone)]
pub struct ReachedStateColor<T: TransitionSystem>(StateColor<T>);

/// Observes the smallest state color that was seen.
pub type LeastStateColor<T> = StateColorLimit<T, false>;
/// Observes the greatest state color that was seen.
pub type GreatestStateColor<T> = StateColorLimit<T, true>;
/// Observes the smallest (`MAX = false`) or greatest (`MAX = true`) state color that was seen.
/// For infinite runs only the colors that appear infinitely often are considered.
#[derive(Debug, Clone)]
pub struct StateColorLimit<T: TransitionSystem, const MAX: bool = false>(pub StateColor<T>);

/// Observes the smallest edge color that was seen.
pub type LeastEdgeColor<T> = EdgeColorLimit<T, false>;
/// Observes the greatest edge color that was seen.
pub type GreatestEdgeColor<T> = EdgeColorLimit<T, true>;
/// Observes the smallest (`MAX = false`) or greatest (`MAX = true`) edge color that was seen.
/// For infinite runs only the colors that appear infinitely often are considered.
#[derive(Debug, Clone)]
pub struct EdgeColorLimit<T: TransitionSystem, const MAX: bool = false>(pub EdgeColor<T>);

/// Observes the set of states that were visited. For infinite runs these are the states that
/// are visited infinitely often.
#[derive(Clone, Debug)]
pub struct StateSet<T: TransitionSystem>(pub(crate) crate::ts::StateSet<StateIndex<T>>);
impl<T: TransitionSystem> std::ops::Deref for StateSet<T> {
    type Target = crate::ts::StateSet<StateIndex<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Observes the sequence of visited states. For infinite runs these are the states along
/// one traversal of the loop.
pub struct StateSequence<T: TransitionSystem>(Vec<StateIndex<T>>);
impl<T: TransitionSystem> std::ops::Deref for StateSequence<T> {
    type Target = Vec<StateIndex<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Observes the sequence of colors of the visited states. For infinite runs these are the
/// colors along one traversal of the loop.
pub struct StateColorSequence<T: TransitionSystem>(Vec<StateColor<T>>);
impl<T: TransitionSystem> std::ops::Deref for StateColorSequence<T> {
    type Target = Vec<StateColor<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Observes the set of colors of visited states. For infinite runs these are the colors
/// that are seen infinitely often.
pub struct StateColorSet<T: TransitionSystem>(math::FxIndexSet<StateColor<T>>);
impl<T: TransitionSystem> std::ops::Deref for StateColorSet<T> {
    type Target = math::FxIndexSet<StateColor<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Observes the set of colors of the taken edges. For infinite runs these are the colors
/// that are seen infinitely often.
#[derive(Debug)]
pub struct EdgeColorSet<T: TransitionSystem>(pub(crate) math::FxIndexSet<EdgeColor<T>>);
impl<T: TransitionSystem> std::ops::Deref for EdgeColorSet<T> {
    type Target = math::FxIndexSet<EdgeColor<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Observes the sequence of colors of the taken edges. For infinite runs these are the
/// colors along one traversal of the loop.
#[derive(Debug)]
pub struct EdgeColorSequence<T: TransitionSystem>(pub(crate) Vec<EdgeColor<T>>);
impl<T: TransitionSystem> std::ops::Deref for EdgeColorSequence<T> {
    type Target = Vec<EdgeColor<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Observes the set of pairs `(state, symbol)` of transitions that were taken. For infinite
/// runs these are the transitions that are taken infinitely often.
#[derive(Debug, Clone)]
pub struct Triggers<T: TransitionSystem>(BTreeSet<(StateIndex<T>, SymbolOf<T>)>);
impl<T: TransitionSystem> std::ops::Deref for Triggers<T> {
    type Target = BTreeSet<(StateIndex<T>, SymbolOf<T>)>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// The run of a deterministic transition system on a word, from a given start state. The
/// constant `FINITE` says whether the word is finite. The observer `O` collects information
/// about the run. Call `evaluate` to execute it.
pub struct Run<
    'ts,
    T: Deterministic,
    W: Word<Symbol = SymbolOf<T>>,
    const FINITE: bool,
    O: Observer<T> = NoObserver,
> {
    ts: &'ts T,
    start: StateIndex<T>,
    word: W,
    observer: PhantomData<O>,
}

impl<T: Deterministic, W: Word<Symbol = SymbolOf<T>>, const FINITE: bool, O: Observer<T>> RunResult
    for Run<'_, T, W, FINITE, O>
{
    type StateColor = StateColor<T>;
    type EdgeColor = EdgeColor<T>;
    type StateIndex = StateIndex<T>;
    type Symbol = SymbolOf<T>;
}

impl<'ts, T: Deterministic, W: FiniteWord<Symbol = SymbolOf<T>>, O: Observer<T>>
    Run<'ts, T, W, true, O>
{
    /// Creates the run of `ts` on the finite word `word` starting in `start`.
    pub fn new_finite(ts: &'ts T, start: StateIndex<T>, word: W) -> Run<'ts, T, W, true, O> {
        Run {
            ts,
            start,
            word,
            observer: PhantomData,
        }
    }
    /// Executes the run. It either reaches a state, or it escapes the transition system on a
    /// symbol for which no transition exists.
    pub fn evaluate(self) -> FiniteRunOutput<T, W, O> {
        let mut taken = 0;
        let mut observer = O::begin(self.ts, self.start);
        let mut current = self.start;

        while let Some(sym) = self.word.nth(taken) {
            taken += 1;
            if let Some(next) = observer.observe_one(self.ts, current, sym) {
                current = next;
            } else {
                return FiniteRunOutput::Failed(current, EscapePrefix::new(self.word, taken));
            }
        }
        FiniteRunOutput::Reached(current, observer.into_current())
    }
    /// Returns true if the run does not escape the transition system.
    pub fn is_successful(self) -> bool {
        matches!(self.evaluate(), FiniteRunOutput::Reached(_, _))
    }
}

impl<'ts, T: Deterministic, W: OmegaWord<Symbol = SymbolOf<T>>, O: InfiniteObserver<T>>
    Run<'ts, T, W, false, O>
{
    /// Creates the run of `ts` on the omega word `word` starting in `start`.
    pub fn new_infinite(ts: &'ts T, start: StateIndex<T>, word: W) -> Run<'ts, T, W, false, O> {
        Run {
            ts,
            start,
            word,
            observer: PhantomData,
        }
    }
    /// Executes the run. It either ends up looping in the transition system, or it escapes it on a
    /// symbol for which no transition exists.
    pub fn evaluate(self) -> InfiniteRunOutput<T, W, O> {
        let spoke = self.word.spoke_vec();
        // first evaluate the finite run piece
        let mut current = match self.ts.finite_run_from::<_, O>(self.start, spoke) {
            FiniteRunOutput::Reached(r, _) => r,
            FiniteRunOutput::Failed(state, ep) => {
                return InfiniteRunOutput::Failed(state, ep.with_word(self.word));
            }
        };

        // only the states at the end of each loop iteration are stored, usually far fewer than
        // there are states, so a dense vector sized by the bound would not pay off
        let mut seen = crate::ts::StateMap::new(None);
        let mut iteration = 0;
        seen.insert(current, iteration);
        let mut seq = vec![];

        let cycle = self.word.cycle_vec();
        loop {
            iteration += 1;
            match self.ts.finite_run_from::<_, O>(current, &cycle) {
                FiniteRunOutput::Reached(reached, output) => {
                    seq.push(output);
                    if let Some(&prev_iteration) = seen.get(&reached) {
                        return InfiniteRunOutput::Successful(O::loop_back(
                            &seq,
                            self.ts,
                            prev_iteration,
                        ));
                    }
                    seen.insert(reached, iteration);
                    current = reached;
                }
                FiniteRunOutput::Failed(reached, ep) => {
                    let length = self.word.spoke_len()
                        + cycle.len() * (iteration - 1)
                        + ep.shortest_escaping_length;
                    return InfiniteRunOutput::Failed(
                        reached,
                        EscapePrefix {
                            word: self.word,
                            shortest_escaping_length: length,
                        },
                    );
                }
            }
        }
    }
    /// Returns true if the run does not escape the transition system.
    pub fn is_successful(self) -> bool {
        matches!(self.evaluate(), InfiniteRunOutput::Successful(_))
    }
}

/// The shortest prefix of a word on which a run leaves a transition system, i.e. after which
/// the next symbol, the *escape symbol*, has no transition. Two escape prefixes are equal if
/// they consist of the same symbols, independent of the word they were taken from.
#[derive(Clone)]
pub struct EscapePrefix<W> {
    word: W,
    shortest_escaping_length: usize,
}

impl<W: Word> EscapePrefix<W> {
    /// Creates an escape prefix of the given `length` (which includes the escape symbol).
    ///
    /// # Panics
    ///
    /// Panics if `length` is zero.
    pub fn new(word: W, length: usize) -> Self {
        assert!(length > 0);
        Self {
            word,
            shortest_escaping_length: length,
        }
    }
    /// Returns the prefix of the word up to and including the escape symbol.
    pub fn as_prefix(&self) -> Infix<'_, W> {
        self.word.prefix(self.shortest_escaping_length)
    }

    /// Replaces the underlying word, keeping the length of the prefix.
    pub fn with_word<V>(self, word: V) -> EscapePrefix<V> {
        EscapePrefix {
            word,
            shortest_escaping_length: self.shortest_escaping_length,
        }
    }
    /// Returns the number of symbols before the escape symbol.
    pub fn len(&self) -> usize {
        self.shortest_escaping_length - 1
    }
    /// Returns true if the escape symbol is the very first symbol of the word.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Sets the length of the prefix, which includes the escape symbol.
    pub fn with_length(self, len: usize) -> Self {
        Self {
            word: self.word,
            shortest_escaping_length: len,
        }
    }
    /// Returns the part of the word that comes after the escape symbol.
    pub fn suffix<S: Symbol>(self) -> ReducedOmegaWord<S>
    where
        W: OmegaWord<Symbol = S>,
    {
        Word::skip(&self.word, self.shortest_escaping_length).reduced()
    }

    /// Returns the symbol on which the transition system is left.
    pub fn escape_symbol(&self) -> W::Symbol {
        self.word.nth(self.shortest_escaping_length - 1).unwrap()
    }
}

impl<W: Word> Word for EscapePrefix<W> {
    type Symbol = W::Symbol;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<W::Symbol> {
        if position + 1 >= self.shortest_escaping_length {
            None
        } else {
            self.word.nth(position)
        }
    }
}
impl<W: Word> FiniteWord for EscapePrefix<W> {
    type Symbols<'this>
        = EscapePrefixSymbols<'this, W>
    where
        Self: 'this;
    fn symbols(&self) -> Self::Symbols<'_> {
        EscapePrefixSymbols(self, 0)
    }
}
/// Iterator over the symbols of an [`EscapePrefix`], excluding the escape symbol.
pub struct EscapePrefixSymbols<'a, W: Word>(&'a EscapePrefix<W>, usize);
impl<W: Word> Iterator for EscapePrefixSymbols<'_, W> {
    type Item = W::Symbol;
    fn next(&mut self) -> Option<Self::Item> {
        if self.1 + 1 >= self.0.shortest_escaping_length {
            None
        } else {
            let out = self.0.nth(self.1).unwrap();
            self.1 += 1;
            Some(out)
        }
    }
}
impl<W: Word> Ord for EscapePrefix<W> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.length_lexicographic_ord(other)
            .then(self.escape_symbol().cmp(&other.escape_symbol()))
    }
}
impl<W: Word> PartialOrd for EscapePrefix<W> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<W: Word> std::hash::Hash for EscapePrefix<W> {
    // must agree with `PartialEq`, which compares the symbols of the prefix; hashing the
    // `Infix` itself would also hash the underlying word and its position
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let prefix = self.as_prefix();
        prefix.len().hash(state);
        for symbol in prefix.symbols() {
            symbol.hash(state);
        }
    }
}

impl<W: Word> PartialEq for EscapePrefix<W> {
    fn eq(&self, other: &Self) -> bool {
        self.as_prefix().finite_word_equals(other.as_prefix())
    }
}
impl<W: Word> Eq for EscapePrefix<W> {}
impl<W: Debug> Debug for EscapePrefix<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "escape prefix length {} of {:?}",
            self.shortest_escaping_length, self.word
        )
    }
}

/// Describes the types that appear in the result of a run.
pub trait RunResult: Sized {
    /// The type of the state colors.
    type StateColor: Color;
    /// The type of the edge colors.
    type EdgeColor: Color;
    /// The type of the state indices.
    type StateIndex: IdType;
    /// The type of symbol over which the input word operates.
    type Symbol: Symbol;
}

/// The result of running a finite word.
pub enum FiniteRunOutput<T: TransitionSystem, W: Word<Symbol = SymbolOf<T>>, O: Observer<T>> {
    /// The run did not escape, it reached the given state with the given observation.
    Reached(StateIndex<T>, O::Current),
    /// The run escaped the transition system from the given state on the given escape prefix.
    Failed(StateIndex<T>, EscapePrefix<W>),
}

impl<T: TransitionSystem, W: Word<Symbol = SymbolOf<T>>, O: Observer<T>> FiniteRunOutput<T, W, O> {
    /// Returns the reached state, or `None` if the run escaped.
    pub fn into_reached_state(self) -> Option<StateIndex<T>> {
        match self {
            FiniteRunOutput::Reached(r, _) => Some(r),
            _ => None,
        }
    }
    /// Returns the observation, or `None` if the run escaped.
    pub fn into_output(self) -> Option<O::Current> {
        match self {
            FiniteRunOutput::Reached(_, o) => Some(o),
            _ => None,
        }
    }
}

/// The result of running an omega word.
pub enum InfiniteRunOutput<
    T: TransitionSystem,
    W: OmegaWord<Symbol = SymbolOf<T>>,
    O: InfiniteObserver<T>,
> {
    /// The run loops in the transition system, with the given observation of the loop.
    Successful(O::Current),
    /// The run escaped the transition system from the given state on the given escape prefix.
    Failed(StateIndex<T>, EscapePrefix<W>),
}

impl<T: TransitionSystem, W: OmegaWord<Symbol = SymbolOf<T>>, O: InfiniteObserver<T>> Debug
    for InfiniteRunOutput<T, W, O>
where
    W: Debug,
    O::Current: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InfiniteRunOutput::Failed(q, esc) => {
                write!(f, "failed from {q:?} with escape prefix {esc:?}")
            }
            InfiniteRunOutput::Successful(ind) => write!(f, "successfully induced {ind:?}"),
        }
    }
}

impl<T: TransitionSystem, W: OmegaWord<Symbol = SymbolOf<T>>, O: InfiniteObserver<T>>
    InfiniteRunOutput<T, W, O>
{
    /// Returns true if the run does not escape the transition system.
    #[inline(always)]
    pub fn is_successful(&self) -> bool {
        matches!(self, InfiniteRunOutput::Successful(_))
    }
    /// Returns true if the run escapes the transition system.
    #[inline(always)]
    pub fn is_escaping(&self) -> bool {
        !self.is_successful()
    }
    /// Returns the observation, or `None` if the run escaped.
    #[inline(always)]
    pub fn into_output(self) -> Option<O::Current> {
        match self {
            Self::Successful(o) => Some(o),
            _ => None,
        }
    }
    /// Returns the state from which the run escaped, or `None` if it did not.
    #[inline(always)]
    pub fn into_escape_state(self) -> Option<StateIndex<T>> {
        match self {
            Self::Failed(state, _phantom) => Some(state),
            _ => None,
        }
    }
    /// Returns the escape prefix, or `None` if the run did not escape.
    #[inline(always)]
    pub fn into_escape_prefix(self) -> Option<EscapePrefix<W>> {
        match self {
            Self::Failed(_, ep) => Some(ep),
            _ => None,
        }
    }
}

mod impls {
    use super::*;
    use crate::TransitionSystem;
    use crate::ts::{Deterministic, EdgeColor, IsEdge, StateColor, StateIndex, SymbolOf};
    use crate::{Lattice, math};

    impl<T: Deterministic> Observer<T> for NoObserver {
        type Current = ();
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &()
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {}
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            NoObserver
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            ts.successor_index(state, sym)
        }
    }

    impl<T: Deterministic> InfiniteObserver<T> for NoObserver {
        fn loop_back(_seq: &[Self::Current], _ts: &T, _time: usize) -> Self::Current {}
    }

    impl<T: Deterministic> Observer<T> for ReachedState<StateIndex<T>> {
        type Current = StateIndex<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn begin(_ts: &T, state: StateIndex<T>) -> Self {
            Self(state)
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            self.0 = ts.successor_index(state, sym)?;
            Some(self.0)
        }
    }
    impl<T: Deterministic> Observer<T> for ReachedStateColor<T> {
        type Current = StateColor<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            Self(ts.state_color(state).unwrap().into_owned())
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let succ = ts.successor_index(state, sym)?;
            self.0.clone_from(&ts.state_color(succ).unwrap());
            Some(succ)
        }
    }
    impl<T: Deterministic> Observer<T> for ReachedEdgeColor<T> {
        type Current = EdgeColor<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            self.0.as_ref().unwrap()
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0.unwrap()
        }
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(None)
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let e = ts.edge(state, sym)?;
            match &mut self.0 {
                Some(c) => c.clone_from(&e.color()),
                none => *none = Some(e.color().into_owned()),
            }
            Some(e.target())
        }
    }
    impl<T: Deterministic<StateColor: Lattice>, const MAX: bool> Observer<T>
        for StateColorLimit<T, MAX>
    {
        type Current = StateColor<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            Self(ts.state_color(state).unwrap().into_owned())
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let succ = ts.successor_index(state, sym)?;
            if MAX {
                self.0.join_assign(&ts.state_color(succ).unwrap());
            } else {
                self.0.meet_assign(&ts.state_color(succ).unwrap());
            }
            Some(succ)
        }
    }
    impl<T: Deterministic<StateColor: Lattice>, const MAX: bool> InfiniteObserver<T>
        for StateColorLimit<T, MAX>
    {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            if MAX {
                Lattice::join_iter(seq[time..].iter())
            } else {
                Lattice::meet_iter(seq[time..].iter())
            }
        }
    }

    impl<T: Deterministic, const MAX: bool> Observer<T> for EdgeColorLimit<T, MAX>
    where
        EdgeColor<T>: Lattice,
    {
        type Current = EdgeColor<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(if MAX {
                Lattice::bottom()
            } else {
                Lattice::top()
            })
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let e = ts.edge(state, sym)?;
            let new = e.color();
            if MAX {
                self.0.join_assign(&new)
            } else {
                self.0.meet_assign(&new)
            }
            Some(e.target())
        }
    }
    impl<T: Deterministic, const MAX: bool> InfiniteObserver<T> for EdgeColorLimit<T, MAX>
    where
        EdgeColor<T>: Lattice,
    {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            if MAX {
                Lattice::join_iter(seq[time..].iter())
            } else {
                Lattice::meet_iter(seq[time..].iter())
            }
        }
    }

    impl<T: TransitionSystem> Default for StateSet<T> {
        fn default() -> Self {
            Self(Default::default())
        }
    }
    impl<T: Deterministic> Observer<T> for StateSet<T> {
        type Current = Self;
        #[inline(always)]
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            let mut set = crate::ts::StateSet::new(ts.state_bound());
            set.insert(state);
            Self(set)
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            self
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor_index = ts.successor_index(state, sym)?;
            self.0.insert(successor_index);
            Some(successor_index)
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for StateSet<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], ts: &T, time: usize) -> Self::Current {
            let mut acc = Self(crate::ts::StateSet::new(ts.state_bound()));
            for x in &seq[time..] {
                acc.0.extend(x.0.iter());
            }
            acc
        }
    }

    impl<T: Deterministic> Observer<T> for StateSequence<T> {
        type Current = Vec<StateIndex<T>>;
        #[inline(always)]
        fn begin(_ts: &T, state: StateIndex<T>) -> Self {
            Self(vec![state])
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor_index = ts.successor_index(state, sym)?;
            self.0.push(successor_index);
            Some(successor_index)
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for StateSequence<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(vec![], |mut acc, x| {
                acc.extend(x);
                acc
            })
        }
    }

    impl<T: Deterministic> Observer<T> for StateColorSequence<T> {
        type Current = Vec<StateColor<T>>;
        #[inline(always)]
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            Self(vec![ts.state_color(state).unwrap().into_owned()])
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor_index = ts.successor_index(state, sym)?;
            self.0
                .push(ts.state_color(successor_index).unwrap().into_owned());
            Some(successor_index)
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for StateColorSequence<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(vec![], |mut acc, x| {
                acc.extend(x.iter().cloned());
                acc
            })
        }
    }

    impl<T: TransitionSystem> Default for StateColorSet<T> {
        fn default() -> Self {
            Self(Default::default())
        }
    }
    impl<T: Deterministic<StateColor: Eq + std::hash::Hash>> Observer<T> for StateColorSet<T> {
        type Current = Self;
        #[inline(always)]
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            let start = ts.state_color(state).unwrap().into_owned();
            Self(math::FxIndexSet::from_iter([start]))
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            self
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let t = ts.edge(state, sym)?;
            let c = ts.state_color(t.target()).unwrap();
            if !self.0.contains(&*c) {
                self.0.insert(c.into_owned());
            }
            Some(t.target())
        }
    }
    impl<T: Deterministic<StateColor: Eq + std::hash::Hash>> InfiniteObserver<T> for StateColorSet<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(Default::default(), |mut acc, x| {
                acc.0.extend(x.0.iter().cloned());
                acc
            })
        }
    }

    impl<T: Deterministic<EdgeColor: Eq + std::hash::Hash>> Observer<T> for EdgeColorSet<T> {
        type Current = Self;
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(math::FxIndexSet::default())
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            self
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let t = ts.edge(state, sym)?;
            let c = t.color();
            if !self.0.contains(&*c) {
                self.0.insert(c.into_owned());
            }
            Some(t.target())
        }
    }
    impl<T: Deterministic<EdgeColor: Eq + std::hash::Hash>> InfiniteObserver<T> for EdgeColorSet<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            Self(
                seq[time..]
                    .iter()
                    .fold(math::FxIndexSet::default(), |mut acc, x| {
                        acc.extend(x.0.iter().cloned());
                        acc
                    }),
            )
        }
    }
    impl<T: Deterministic> Clone for EdgeColorSet<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    impl<T: Deterministic> Observer<T> for EdgeColorSequence<T> {
        type Current = Vec<EdgeColor<T>>;
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(vec![])
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let t = ts.edge(state, sym)?;
            self.0.push(t.color().into_owned());
            Some(t.target())
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for EdgeColorSequence<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(
                Vec::with_capacity((seq.len() - time) * seq[time].len()),
                |mut acc, x| {
                    acc.extend(x.iter().cloned());
                    acc
                },
            )
        }
    }
    impl<T: Deterministic> Clone for EdgeColorSequence<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    impl<T: Deterministic> Observer<T> for Triggers<T> {
        type Current = BTreeSet<(StateIndex<T>, SymbolOf<T>)>;

        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }

        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }

        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(BTreeSet::default())
        }

        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor = ts.successor_index(state, sym)?;
            self.0.insert((state, sym));
            Some(successor)
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for Triggers<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            assert!(!seq.is_empty());
            assert!(time < seq.len());

            seq[time..].iter().fold(BTreeSet::default(), |mut acc, x| {
                acc.extend(x.iter().cloned());
                acc
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ts::run::EscapePrefix;
    use crate::ts::{Builder, Deterministic, IsEdge, TransitionSystem};

    #[test]
    fn run_escaping() {
        let dts = Builder::without_colors()
            .with_transitions([(0, 'a', 1), (1, 'a', 0)])
            .into_dts_with_initial(0);

        let w0 = upw!("a");
        assert_eq!(dts.omega_escape_prefix(&w0), None);
        let w1 = upw!("a", "b");
        assert_eq!(
            dts.omega_escape_prefix(&w1),
            Some(EscapePrefix::new(&w1, 2))
        );
    }

    #[test]
    fn escape_prefix_of_length_zero_is_empty() {
        let dts = Builder::without_colors()
            .with_transitions([(0, 'a', 1), (1, 'a', 0)])
            .into_dts_with_initial(0);
        let word = upw!("b");
        let escape = dts.omega_escape_prefix(&word).expect("must escape");
        assert_eq!(escape.len(), 0);
        assert!(escape.is_empty());
        let longer = dts.omega_escape_prefix(upw!("a", "b")).unwrap();
        assert_eq!(longer.len(), 1);
        assert!(!longer.is_empty());
    }

    #[test]
    fn state_color_limits_of_infinite_runs() {
        use crate::ts::run::{GreatestStateColor, LeastStateColor};

        // the cycle 1 -> 2 -> 3 -> 1 has the state colors 2, 7, 4, state 0 (color 1) is left for good
        let dts = Builder::without_edge_colors()
            .with_state_colors([1u8, 2, 7, 4])
            .with_transitions([(0, 'a', 1), (1, 'a', 2), (2, 'a', 3), (3, 'a', 1)])
            .into_dts_with_initial(0);

        let word = upw!("a");
        let greatest = dts
            .omega_run::<_, GreatestStateColor<_>>(&word)
            .into_output()
            .unwrap();
        let least = dts
            .omega_run::<_, LeastStateColor<_>>(&word)
            .into_output()
            .unwrap();
        assert_eq!(greatest, 7);
        assert_eq!(least, 2);
    }

    #[test]
    fn float_edge_colors_can_be_built_and_run() {
        // `f64` is neither `Eq` nor `Hash`, which must not matter for building and running
        let dts = Builder::without_state_colors()
            .with_transitions([(0, 'a', 0.5f64, 1), (1, 'a', 1.5, 0)])
            .into_dts_with_initial(0);

        assert_eq!(dts.last_edge_color("aa"), Some(1.5));
        assert_eq!(dts.visited_edge_colors("aaa"), Some(vec![0.5, 1.5, 0.5]));
        assert_eq!(
            TransitionSystem::edges_from(dts.ts(), 0)
                .unwrap()
                .next()
                .unwrap()
                .color()
                .into_owned(),
            0.5
        );
    }
}
