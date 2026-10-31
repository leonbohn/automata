use crate::{
    alphabet::Symbol,
    math,
    word::Infix,
    word::{Finite, FiniteWord, Omega, OmegaWord, ReducedOmegaWord, Word},
};
use std::collections::BTreeSet;
use std::fmt::Debug;

use crate::TransitionSystem;
use crate::ts::{Deterministic, EdgeColor, StateColor, StateIndex, SymbolOf};

/// Observes a run on a [`TransitionSystem`] and collects information about it, for example the
/// state that is reached or the colors that are seen. A run feeds the symbols of a word one by
/// one to the observer, which also takes the transition.
///
/// For an infinite word the observer sees the cycle that the run ends up in, starting in a state
/// of that cycle and going around it once. What the run does before that is not observed.
pub trait Observer<T: TransitionSystem>: Sized {
    /// The information that the observer collects.
    type Current;
    /// Whether the observer looks at the transitions at all. Passes through the cycle of an
    /// infinite word are only kept for an observer that does.
    const OBSERVES: bool = true;
    /// Consumes the observer and returns the collected information.
    fn into_current(self) -> Self::Current;
    /// Adds what `later` has observed to `self`, where `later` observed the part of the run that
    /// directly follows the part observed by `self`. A run on an infinite word observes each pass
    /// through the cycle of the word with its own observer and merges those of the loop.
    fn merge(&mut self, later: Self);
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

/// Observes the sequence of colors of the taken edges.
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

/// The run of a deterministic transition system on a word, from a start state. It is created
/// by [`Deterministic::run`] and executed by one of the methods that consume it. Whether the word
/// is finite or infinite is determined by its type ([`Word::Kind`]):
///
/// ```
/// use automata::{ts::{Builder, Deterministic, run::EdgeColorSet}, upw};
///
/// let ts = Builder::without_state_colors()
///     .with_transitions([(0, 'a', 1u8, 1), (1, 'b', 2, 0)])
///     .into_dts_with_initial(0);
///
/// assert_eq!(ts.run("ab").reached_state(), Some(0));
/// let colors = ts.run_from(1, upw!("ba")).observe::<EdgeColorSet<_>>();
/// assert_eq!(colors.unwrap().len(), 2);
/// assert!(ts.run(upw!("b")).escape_prefix().is_some());
/// ```
///
/// A run on an infinite word does not allocate, except for what the observer needs.
#[derive(Debug, Clone)]
pub struct Run<'ts, T: Deterministic, W> {
    ts: &'ts T,
    start: StateIndex<T>,
    word: W,
}

/// Executes a run for the kind of word ([`Finite`] or [`Omega`]) that implements it. This is
/// what lets [`Run`] have the same methods for finite and infinite words.
pub trait RunKind<T: Deterministic, W> {
    /// Runs `word` from `start` and returns what the observer `O` has collected, or the
    /// length of the shortest prefix after which the run escapes (including the escape symbol).
    fn run<O: Observer<T>>(ts: &T, start: StateIndex<T>, word: &W) -> Result<O::Current, usize>;
}

impl<T: Deterministic, W: FiniteWord<Symbol = SymbolOf<T>>> RunKind<T, W> for Finite {
    #[inline]
    fn run<O: Observer<T>>(ts: &T, start: StateIndex<T>, word: &W) -> Result<O::Current, usize> {
        let mut observer = O::begin(ts, start);
        let mut current = start;
        for (position, sym) in word.symbols().enumerate() {
            current = observer.observe_one(ts, current, sym).ok_or(position + 1)?;
        }
        Ok(observer.into_current())
    }
}

impl<T: Deterministic, W: OmegaWord<Symbol = SymbolOf<T>>> RunKind<T, W> for Omega {
    fn run<O: Observer<T>>(ts: &T, start: StateIndex<T>, word: &W) -> Result<O::Current, usize> {
        let cycle = word.cycle();
        let cycle_len = cycle.len();
        assert!(cycle_len > 0, "word must be infinite");

        let mut current = start;
        let mut taken = 0usize;
        for sym in word.spoke().symbols() {
            taken += 1;
            current = ts.successor(current, sym).ok_or(taken)?;
        }

        // Each pass through the cycle of the word has its own observer. The states at the ends of
        // the passes tell which of them form the loop of the run, those are merged.
        let mut seen = crate::ts::StateMap::new(None);
        let mut passes = Vec::new();
        let mut count = 0usize;
        seen.insert(current, count);
        loop {
            let mut observer = O::begin(ts, current);
            for sym in cycle.symbols() {
                taken += 1;
                current = observer.observe_one(ts, current, sym).ok_or(taken)?;
            }
            count += 1;
            if O::OBSERVES {
                passes.push(observer);
            }
            if let Some(&first) = seen.get(&current) {
                let mut loop_passes = passes.drain(first.min(passes.len())..);
                return Ok(match loop_passes.next() {
                    Some(mut merged) => {
                        loop_passes.for_each(|pass| merged.merge(pass));
                        merged.into_current()
                    }
                    None => O::begin(ts, current).into_current(),
                });
            }
            seen.insert(current, count);
        }
    }
}

impl<'ts, T: Deterministic, W: Word<Symbol = SymbolOf<T>>> Run<'ts, T, W> {
    /// Creates the run of `ts` on `word` starting in `start`.
    pub fn new(ts: &'ts T, start: StateIndex<T>, word: W) -> Self {
        Self { ts, start, word }
    }

    /// Executes the run. It either completes, with what the observer `O` has collected (for
    /// an infinite word that is the cycle of the run), or it escapes the transition system on a
    /// symbol for which no transition exists.
    pub fn evaluate<O: Observer<T>>(self) -> RunOutput<W, O::Current>
    where
        W::Kind: RunKind<T, W>,
    {
        match <W::Kind as RunKind<T, W>>::run::<O>(self.ts, self.start, &self.word) {
            Ok(observed) => RunOutput::Reached(observed),
            Err(length) => RunOutput::Escaped(EscapePrefix::new(self.word, length)),
        }
    }

    /// Executes the run and returns what the observer `O` has collected, or `None` if the run
    /// escapes the transition system. A run that starts in a state that does not exist escapes,
    /// even on the empty word.
    #[inline]
    pub fn observe<O: Observer<T>>(self) -> Option<O::Current>
    where
        W::Kind: RunKind<T, W>,
    {
        self.ts.state_color(self.start)?;
        <W::Kind as RunKind<T, W>>::run::<O>(self.ts, self.start, &self.word).ok()
    }

    /// Returns true if the run does not escape the transition system.
    #[inline]
    pub fn is_successful(self) -> bool
    where
        W::Kind: RunKind<T, W>,
    {
        self.observe::<NoObserver>().is_some()
    }

    /// Returns the shortest prefix of the word after which the run escapes the transition
    /// system, or `None` if it does not escape.
    #[inline]
    pub fn escape_prefix(self) -> Option<EscapePrefix<W>>
    where
        W::Kind: RunKind<T, W>,
    {
        self.evaluate::<NoObserver>().into_escape_prefix()
    }
}

impl<T: Deterministic, W: FiniteWord<Symbol = SymbolOf<T>>> Run<'_, T, W> {
    /// Returns the state that is reached, or `None` if the run escapes.
    #[inline]
    pub fn reached_state(self) -> Option<StateIndex<T>> {
        self.observe::<ReachedState<StateIndex<T>>>()
    }
    /// Returns the color of the state that is reached, or `None` if the run escapes.
    #[inline]
    pub fn reached_state_color(self) -> Option<StateColor<T>> {
        self.observe::<ReachedStateColor<T>>()
    }
    /// Returns the color of the last edge that is taken, or `None` if the run escapes.
    ///
    /// # Panics
    ///
    /// Panics if the word is empty, as there is no such edge then.
    #[inline]
    pub fn last_edge_color(self) -> Option<EdgeColor<T>> {
        self.observe::<ReachedEdgeColor<T>>()
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
    ///
    /// # Panics
    /// Panics if `len` is zero, as the escape symbol is part of the prefix.
    pub fn with_length(self, len: usize) -> Self {
        assert!(len > 0, "the prefix includes the escape symbol");
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
    ///
    /// # Panics
    /// Panics if the word is shorter than the prefix, which can only happen if the word was
    /// replaced with [`Self::with_word`] or the length changed with [`Self::with_length`].
    pub fn escape_symbol(&self) -> W::Symbol {
        self.word
            .nth(self.shortest_escaping_length - 1)
            .expect("the word contains the escape symbol")
    }
}

impl<W: Word> Word for EscapePrefix<W> {
    type Symbol = W::Symbol;
    const FINITE: bool = true;
    type Kind = crate::word::Finite;
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

/// The result of a [`Run`].
pub enum RunOutput<W, C> {
    /// The run did not escape, with what the observer has collected.
    Reached(C),
    /// The run escaped the transition system on the given escape prefix.
    Escaped(EscapePrefix<W>),
}

impl<W, C> RunOutput<W, C> {
    /// Returns true if the run does not escape the transition system.
    #[inline(always)]
    pub fn is_successful(&self) -> bool {
        matches!(self, RunOutput::Reached(_))
    }
    /// Returns true if the run escapes the transition system.
    #[inline(always)]
    pub fn is_escaping(&self) -> bool {
        !self.is_successful()
    }
    /// Returns the observation, or `None` if the run escaped.
    #[inline(always)]
    pub fn into_output(self) -> Option<C> {
        match self {
            Self::Reached(c) => Some(c),
            _ => None,
        }
    }
    /// Returns the escape prefix, or `None` if the run did not escape.
    #[inline(always)]
    pub fn into_escape_prefix(self) -> Option<EscapePrefix<W>> {
        match self {
            Self::Escaped(ep) => Some(ep),
            _ => None,
        }
    }
}

impl<W: Debug, C: Debug> Debug for RunOutput<W, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunOutput::Escaped(esc) => write!(f, "escaped with {esc:?}"),
            RunOutput::Reached(observed) => write!(f, "reached {observed:?}"),
        }
    }
}

mod impls {
    use super::*;
    use crate::ts::{Deterministic, EdgeColor, StateColor, StateIndex, SymbolOf};
    use crate::{Lattice, math};

    impl<T: Deterministic> Observer<T> for NoObserver {
        #[inline(always)]
        fn merge(&mut self, _later: Self) {}
        type Current = ();
        const OBSERVES: bool = false;
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
            ts.successor(state, sym)
        }
    }

    impl<T: Deterministic> Observer<T> for ReachedState<StateIndex<T>> {
        #[inline(always)]
        fn merge(&mut self, later: Self) {
            self.0 = later.0;
        }
        type Current = StateIndex<T>;
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
            self.0 = ts.successor(state, sym)?;
            Some(self.0)
        }
    }
    impl<T: Deterministic> Observer<T> for ReachedStateColor<T> {
        #[inline(always)]
        fn merge(&mut self, later: Self) {
            self.0 = later.0;
        }
        type Current = StateColor<T>;
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
            let succ = ts.successor(state, sym)?;
            self.0.clone_from(&ts.state_color(succ).unwrap());
            Some(succ)
        }
    }
    impl<T: Deterministic> Observer<T> for ReachedEdgeColor<T> {
        #[inline(always)]
        fn merge(&mut self, later: Self) {
            self.0 = later.0.or(self.0.take());
        }
        type Current = EdgeColor<T>;
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
                Some(c) => c.clone_from(e.color()),
                none => *none = Some(e.color().clone()),
            }
            Some(e.target())
        }
    }
    impl<T: Deterministic<StateColor: Lattice>, const MAX: bool> Observer<T>
        for StateColorLimit<T, MAX>
    {
        #[inline(always)]
        fn merge(&mut self, later: Self) {
            if MAX {
                self.0.join_assign(&later.0)
            } else {
                self.0.meet_assign(&later.0)
            }
        }
        type Current = StateColor<T>;
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
            let succ = ts.successor(state, sym)?;
            if MAX {
                self.0.join_assign(&ts.state_color(succ).unwrap());
            } else {
                self.0.meet_assign(&ts.state_color(succ).unwrap());
            }
            Some(succ)
        }
    }

    impl<T: Deterministic, const MAX: bool> Observer<T> for EdgeColorLimit<T, MAX>
    where
        EdgeColor<T>: Lattice,
    {
        #[inline(always)]
        fn merge(&mut self, later: Self) {
            if MAX {
                self.0.join_assign(&later.0)
            } else {
                self.0.meet_assign(&later.0)
            }
        }
        type Current = EdgeColor<T>;
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
                self.0.join_assign(new)
            } else {
                self.0.meet_assign(new)
            }
            Some(e.target())
        }
    }

    impl<T: Deterministic> Observer<T> for StateSet<T> {
        #[inline(always)]
        fn merge(&mut self, later: Self) {
            self.0.extend(later.0.iter());
        }
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
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor = ts.successor(state, sym)?;
            self.0.insert(successor);
            Some(successor)
        }
    }

    impl<T: Deterministic<EdgeColor: Eq + std::hash::Hash>> Observer<T> for EdgeColorSet<T> {
        #[inline(always)]
        fn merge(&mut self, later: Self) {
            self.0.extend(later.0);
        }
        type Current = Self;
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(math::FxIndexSet::default())
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
            if !self.0.contains(c) {
                self.0.insert(c.clone());
            }
            Some(t.target())
        }
    }
    impl<T: Deterministic> Clone for EdgeColorSet<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    impl<T: Deterministic> Observer<T> for EdgeColorSequence<T> {
        #[inline(always)]
        fn merge(&mut self, later: Self) {
            self.0.extend(later.0);
        }
        type Current = Vec<EdgeColor<T>>;
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(vec![])
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
            self.0.push(t.color().clone());
            Some(t.target())
        }
    }
    impl<T: Deterministic> Clone for EdgeColorSequence<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    impl<T: Deterministic> Observer<T> for Triggers<T> {
        #[inline(always)]
        fn merge(&mut self, later: Self) {
            self.0.extend(later.0);
        }
        type Current = BTreeSet<(StateIndex<T>, SymbolOf<T>)>;

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
            let successor = ts.successor(state, sym)?;
            self.0.insert((state, sym));
            Some(successor)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ts::run::EscapePrefix;
    use crate::ts::{Builder, Deterministic, TransitionSystem};

    #[test]
    fn run_escaping() {
        let dts = Builder::without_colors()
            .with_transitions([(0, 'a', 1), (1, 'a', 0)])
            .into_dts_with_initial(0);

        let w0 = upw!("a");
        assert_eq!(dts.run(&w0).escape_prefix(), None);
        let w1 = upw!("a", "b");
        assert_eq!(
            dts.run(&w1).escape_prefix(),
            Some(EscapePrefix::new(&w1, 2))
        );
    }

    #[test]
    fn run_from_missing_state_escapes_even_on_the_empty_word() {
        let dts = Builder::without_colors()
            .with_transitions([(0, 'a', 1), (1, 'a', 0)])
            .into_dts_with_initial(0);

        assert_eq!(dts.reached_state_from(0, ""), Some(0));
        assert_eq!(dts.reached_state_from(7, ""), None);
        assert_eq!(dts.reached_state_from(7, "a"), None);
        assert!(!dts.run_from(7, "").is_successful());
    }

    #[test]
    fn omega_run_observes_only_the_cycle_of_the_run() {
        use crate::ts::run::EdgeColorSet;

        // a^ω goes through the passes 0, 1, 2, 3, 4, 2, ...; only the colors 3, 4, 5 are in the cycle
        let dts = Builder::without_state_colors()
            .with_transitions([
                (0, 'a', 1u8, 1),
                (1, 'a', 2, 2),
                (2, 'a', 3, 3),
                (3, 'a', 4, 4),
                (4, 'a', 5, 2),
            ])
            .into_dts_with_initial(0);

        let colors = dts.run(upw!("a")).observe::<EdgeColorSet<_>>().unwrap();
        let mut colors: Vec<_> = colors.iter().copied().collect();
        colors.sort();
        assert_eq!(colors, vec![3, 4, 5]);
        // a cycle that is a multiple of the period of the run gives the same result
        let colors = dts.run(upw!("a", "aaaaaa")).observe::<EdgeColorSet<_>>();
        assert_eq!(colors.unwrap().len(), 3);
    }

    #[test]
    fn omega_run_escapes_in_a_later_pass_of_the_cycle() {
        // the cycle ab runs through 0, 1, 2, 3, 4, which has no transition on a: escape after 4 symbols
        let dts = Builder::without_colors()
            .with_transitions([(0, 'a', 1), (1, 'b', 2), (2, 'a', 3), (3, 'b', 4)])
            .into_dts_with_initial(0);
        let word = upw!("ab");
        let escape = dts.run(&word).escape_prefix().expect("must escape");
        assert_eq!(escape.len(), 4);
    }

    #[test]
    fn escape_prefix_of_length_zero_is_empty() {
        let dts = Builder::without_colors()
            .with_transitions([(0, 'a', 1), (1, 'a', 0)])
            .into_dts_with_initial(0);
        let word = upw!("b");
        let escape = dts.run(&word).escape_prefix().expect("must escape");
        assert_eq!(escape.len(), 0);
        assert!(escape.is_empty());
        let longer = dts.run(upw!("a", "b")).escape_prefix().unwrap();
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
        let greatest = dts.run(&word).observe::<GreatestStateColor<_>>().unwrap();
        let least = dts.run(&word).observe::<LeastStateColor<_>>().unwrap();
        assert_eq!(greatest, 7);
        assert_eq!(least, 2);
    }

    #[test]
    fn float_edge_colors_can_be_built_and_run() {
        // `f64` is neither `Eq` nor `Hash`, which must not matter for building and running
        let dts = Builder::without_state_colors()
            .with_transitions([(0, 'a', 0.5f64, 1), (1, 'a', 1.5, 0)])
            .into_dts_with_initial(0);

        assert_eq!(dts.run("aa").last_edge_color(), Some(1.5));
        assert_eq!(
            dts.run("aaa")
                .observe::<crate::ts::run::EdgeColorSequence<_>>(),
            Some(vec![0.5, 1.5, 0.5])
        );
        assert_eq!(
            TransitionSystem::edges_from(dts.ts(), 0)
                .unwrap()
                .next()
                .unwrap()
                .color()
                .clone(),
            0.5
        );
    }
}
