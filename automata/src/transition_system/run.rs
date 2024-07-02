#![allow(missing_docs)]
use std::{fmt::Debug, marker::PhantomData};

use crate::prelude::*;

pub trait Observer<T: TransitionSystem>: Sized {
    type Current;
    fn current(&self) -> &Self::Current;
    fn into_current(self) -> Self::Current;
    fn begin(ts: &T, state: StateIndex<T>) -> Self;
    fn observe(&mut self, ts: &T, state: StateIndex<T>, sym: SymbolOf<T>) -> Option<StateIndex<T>>;
}

pub trait InfiniteObserver<T: TransitionSystem>: Observer<T> {
    fn loop_back(seq: &[Self::Current], ts: &T, time: usize) -> Self::Current;
}

#[derive(Debug, Clone, Copy)]
pub struct NoObserver;
#[derive(Debug, Clone, Copy)]
pub struct ReachedState<Idx>(Idx);
#[derive(Debug, Clone)]
pub struct ReachedEdgeColor<T: TransitionSystem>(Option<EdgeColor<T>>);
#[derive(Debug, Clone)]
pub struct ReachedStateColor<T: TransitionSystem>(StateColor<T>);
#[derive(Debug, Clone)]
pub struct LeastStateColor<Q>(Q);
pub type LeastEdgeColor<T> = EdgeColorLimit<T, false>;
pub type GreatestEdgeColor<T> = EdgeColorLimit<T, true>;
pub struct EdgeColorLimit<T: TransitionSystem, const MAX: bool = false>(Option<EdgeColor<T>>);

#[derive(Clone, Debug)]
pub struct StateSet<T: TransitionSystem>(math::Set<StateIndex<T>>);

pub struct StateSequence<T: TransitionSystem>(Vec<StateIndex<T>>);

pub struct StateColorSequence<T: TransitionSystem>(Vec<StateColor<T>>);

pub struct StateColorSet<T: TransitionSystem>(math::Set<StateColor<T>>);

#[derive(Debug)]
pub struct EdgeColorSet<T: TransitionSystem>(pub(crate) math::Set<EdgeColor<T>>);

#[derive(Debug)]
pub struct EdgeColorSequence<T: TransitionSystem>(pub(crate) Vec<EdgeColor<T>>);

#[derive(Debug, Clone)]
pub struct Triggers<T: TransitionSystem>(math::Set<(StateIndex<T>, SymbolOf<T>)>);

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

impl<'ts, T: Deterministic, W: Word<Symbol = SymbolOf<T>>, const FINITE: bool, O: Observer<T>>
    RunResult for Run<'ts, T, W, FINITE, O>
{
    type StateColor = StateColor<T>;
    type EdgeColor = EdgeColor<T>;
    type StateIndex = StateIndex<T>;
    type Symbol = SymbolOf<T>;
}

impl<'ts, T: Deterministic, W: FiniteWord<Symbol = SymbolOf<T>>, O: Observer<T>>
    Run<'ts, T, W, true, O>
{
    pub fn new_finite(ts: &'ts T, start: StateIndex<T>, word: W) -> Run<'ts, T, W, true, O> {
        Run {
            ts,
            start,
            word,
            observer: PhantomData,
        }
    }
    pub fn evaluate(self) -> FiniteRunOutput<T, W, O> {
        let mut taken = 0;
        let mut observer = O::begin(self.ts, self.start);
        let mut current = self.start;

        while let Some(sym) = self.word.nth(taken) {
            if let Some(next) = observer.observe(self.ts, current, sym) {
                current = next;
            } else {
                return FiniteRunOutput::Failed(
                    current,
                    EscapePrefix {
                        word: self.word,
                        length: taken,
                    },
                );
            }
            taken += 1;
        }
        FiniteRunOutput::Reached(current, observer.into_current())
    }
    pub fn is_successful(self) -> bool {
        matches!(self.evaluate(), FiniteRunOutput::Reached(_, _))
    }
}

impl<'ts, T: Deterministic, W: OmegaWord<Symbol = SymbolOf<T>>, O: InfiniteObserver<T>>
    Run<'ts, T, W, false, O>
{
    pub fn new_infinite(ts: &'ts T, start: StateIndex<T>, word: W) -> Run<'ts, T, W, false, O> {
        Run {
            ts,
            start,
            word,
            observer: PhantomData,
        }
    }
    pub fn evaluate(self) -> InfiniteRunOutput<T, W, O> {
        let spoke = self.word.spoke_vec();
        // first evaluate the finite run piece
        let mut current = match self.ts.finite_run_from::<_, O>(self.start, spoke) {
            FiniteRunOutput::Reached(r, _) => r,
            FiniteRunOutput::Failed(state, ep) => {
                return InfiniteRunOutput::Failed(state, ep.with_word(self.word))
            }
        };

        let mut seen = math::Map::default();
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
                    let length =
                        self.word.spoke_length() + cycle.len() * (iteration - 1) + ep.length;
                    return InfiniteRunOutput::Failed(
                        reached,
                        EscapePrefix {
                            word: self.word,
                            length,
                        },
                    );
                }
            }
        }
    }
    pub fn is_successful(self) -> bool {
        matches!(self.evaluate(), InfiniteRunOutput::Successful(_))
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct EscapePrefix<W> {
    pub word: W,
    length: usize,
}

impl<W: Word> EscapePrefix<W> {
    pub fn new(word: W, length: usize) -> Self {
        Self { word, length }
    }

    pub fn with_word<V>(self, word: V) -> EscapePrefix<V> {
        EscapePrefix {
            word,
            length: self.length,
        }
    }
    pub fn len(&self) -> usize {
        self.length
    }
    pub fn with_length(self, len: usize) -> Self {
        Self {
            word: self.word,
            length: len,
        }
    }
    pub fn suffix<S: Symbol>(self) -> ReducedOmegaWord<S>
    where
        W: OmegaWord<Symbol = S>,
    {
        Word::skip(&self.word, self.length).reduced()
    }

    pub fn escape_symbol(&self) -> W::Symbol {
        self.word.nth(self.length).unwrap()
    }
}

impl<W: Word> Word for EscapePrefix<W> {
    type Symbol = W::Symbol;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<W::Symbol> {
        if position >= self.length {
            None
        } else {
            self.word.nth(position)
        }
    }
}
impl<W: Word> FiniteWord for EscapePrefix<W> {
    type Symbols<'this> = EscapePrefixSymbols<'this, W> where Self: 'this;
    fn symbols(&self) -> Self::Symbols<'_> {
        EscapePrefixSymbols(self, 0)
    }
}
pub struct EscapePrefixSymbols<'a, W: Word>(&'a EscapePrefix<W>, usize);
impl<'a, W: Word> Iterator for EscapePrefixSymbols<'a, W> {
    type Item = W::Symbol;
    fn next(&mut self) -> Option<Self::Item> {
        if self.1 >= self.0.length {
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
        self.length.cmp(&other.length).then(
            self.word
                .prefix(self.length)
                .collect_vec()
                .cmp(&other.word.prefix(self.length).collect_vec()),
        )
    }
}
impl<W: Word> PartialOrd for EscapePrefix<W> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}
impl<W: Debug> Debug for EscapePrefix<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "escape prefix length {} of {:?}", self.length, self.word)
    }
}

pub trait RunResult: Sized {
    /// The type of the state colors.
    type StateColor: Color;
    /// The type of the edge colors.
    type EdgeColor: Color;
    /// The type of the state indices.
    type StateIndex: IndexType;
    /// The type of symbol over which the input word operates.
    type Symbol: Symbol;
    // fn reduced<R:
}

pub enum FiniteRunOutput<T: TransitionSystem, W: Word<Symbol = SymbolOf<T>>, O: Observer<T>> {
    Reached(StateIndex<T>, O::Current),
    Failed(StateIndex<T>, EscapePrefix<W>),
}

impl<T: TransitionSystem, W: Word<Symbol = SymbolOf<T>>, O: Observer<T>> FiniteRunOutput<T, W, O> {
    /// Returns the state from which the transition system is left.
    #[allow(unused)]
    fn escape_state(&self) -> Option<StateIndex<T>> {
        match self {
            FiniteRunOutput::Reached(_, _) => None,
            FiniteRunOutput::Failed(state, _) => Some(*state),
        }
    }
    /// Returns the [`EscapePrefix`] with which the ts is left.
    #[allow(unused)]
    fn escape_prefix(&self) -> Option<&EscapePrefix<W>> {
        match self {
            FiniteRunOutput::Reached(_, _) => None,
            FiniteRunOutput::Failed(_state, ep) => Some(ep),
        }
    }
    pub fn into_reached_state(self) -> Option<StateIndex<T>> {
        match self {
            FiniteRunOutput::Reached(r, _) => Some(r),
            _ => None,
        }
    }
    pub fn into_output(self) -> Option<O::Current> {
        match self {
            FiniteRunOutput::Reached(_, o) => Some(o),
            _ => None,
        }
    }
}

pub enum InfiniteRunOutput<
    T: TransitionSystem,
    W: OmegaWord<Symbol = SymbolOf<T>>,
    O: InfiniteObserver<T>,
> {
    Successful(O::Current),
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
    pub fn is_successful(&self) -> bool {
        matches!(self, InfiniteRunOutput::Successful(_))
    }
    pub fn into_output(self) -> Option<O::Current> {
        match self {
            Self::Successful(o) => Some(o),
            _ => None,
        }
    }
    pub fn into_escape_state(self) -> Option<StateIndex<T>> {
        match self {
            Self::Failed(state, _phantom) => Some(state),
            _ => None,
        }
    }
    pub fn into_escape_prefix(self) -> Option<EscapePrefix<W>> {
        match self {
            Self::Failed(_, ep) => Some(ep),
            _ => None,
        }
    }
}

mod impls {
    use super::*;

    impl<T: Deterministic> Observer<T> for NoObserver {
        type Current = ();
        fn current(&self) -> &Self::Current {
            &()
        }
        fn into_current(self) -> Self::Current {
            ()
        }
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            NoObserver
        }
        fn observe(
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
        fn current(&self) -> &Self::Current {
            &self.0
        }
        fn begin(_ts: &T, state: StateIndex<T>) -> Self {
            Self(state)
        }
        fn into_current(self) -> Self::Current {
            self.0
        }
        fn observe(
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
        fn current(&self) -> &Self::Current {
            &self.0
        }
        fn into_current(self) -> Self::Current {
            self.0
        }
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            Self(ts.state_color(state).unwrap())
        }
        fn observe(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let succ = ts.successor_index(state, sym)?;
            self.0 = ts.state_color(succ).unwrap();
            Some(succ)
        }
    }
    impl<T: Deterministic> Observer<T> for ReachedEdgeColor<T> {
        type Current = EdgeColor<T>;
        fn current(&self) -> &Self::Current {
            self.0.as_ref().unwrap()
        }
        fn into_current(self) -> Self::Current {
            self.0.unwrap()
        }
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(None)
        }
        fn observe(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let e = ts.edge(state, sym)?;
            self.0 = Some(e.color());
            Some(e.target())
        }
    }

    impl<T: Deterministic<StateColor: Ord>> Observer<T> for LeastStateColor<StateColor<T>> {
        type Current = StateColor<T>;
        fn current(&self) -> &Self::Current {
            &self.0
        }
        fn into_current(self) -> Self::Current {
            self.0
        }
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            Self(ts.state_color(state).unwrap())
        }
        fn observe(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let succ = ts.successor_index(state, sym)?;
            self.0 = std::cmp::min(ts.state_color(succ).unwrap(), self.0.clone());
            Some(succ)
        }
    }
    impl<T: Deterministic<StateColor: Ord>> InfiniteObserver<T> for LeastStateColor<StateColor<T>>
    where
        StateColor<T>: Default + Ord,
    {
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..]
                .iter()
                .min()
                .expect("looping sequence must not be empty")
                .clone()
        }
    }

    impl<T: Deterministic, const MAX: bool> Observer<T> for EdgeColorLimit<T, MAX>
    where
        EdgeColor<T>: Ord,
    {
        type Current = Option<EdgeColor<T>>;
        fn current(&self) -> &Self::Current {
            &self.0
        }
        fn into_current(self) -> Self::Current {
            self.0
        }
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(None)
        }
        fn observe(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let e = ts.edge(state, sym)?;
            let mut new = e.color();
            if let Some(old) = self.0.take() {
                new = if MAX {
                    std::cmp::max(new, old)
                } else {
                    std::cmp::min(new, old)
                };
            }
            self.0 = Some(new);
            Some(e.target())
        }
    }
    impl<T: Deterministic, const MAX: bool> InfiniteObserver<T> for EdgeColorLimit<T, MAX>
    where
        EdgeColor<T>: Ord,
    {
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().min().unwrap().clone()
        }
    }

    impl<T: TransitionSystem> Default for StateSet<T> {
        fn default() -> Self {
            Self(Default::default())
        }
    }
    impl<T: Deterministic> Observer<T> for StateSet<T> {
        type Current = Self;
        fn begin(_ts: &T, state: StateIndex<T>) -> Self {
            Self(math::Set::from_iter([state]))
        }
        fn into_current(self) -> Self::Current {
            self
        }
        fn current(&self) -> &Self::Current {
            &self
        }
        fn observe(
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
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(Default::default(), |mut acc, x| {
                acc.0.extend(x.0.iter().cloned());
                acc
            })
        }
    }

    impl<T: Deterministic> Observer<T> for StateSequence<T> {
        type Current = Vec<StateIndex<T>>;
        fn begin(_ts: &T, state: StateIndex<T>) -> Self {
            Self(vec![state])
        }
        fn current(&self) -> &Self::Current {
            &self.0
        }
        fn into_current(self) -> Self::Current {
            self.0
        }
        fn observe(
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
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(vec![], |mut acc, x| {
                acc.extend(x);
                acc
            })
        }
    }

    impl<T: Deterministic> Observer<T> for StateColorSequence<T> {
        type Current = Vec<StateColor<T>>;
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            Self(vec![ts.state_color(state).unwrap()])
        }
        fn current(&self) -> &Self::Current {
            &self.0
        }
        fn into_current(self) -> Self::Current {
            self.0
        }
        fn observe(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor_index = ts.successor_index(state, sym)?;
            self.0.push(ts.state_color(successor_index).unwrap());
            Some(successor_index)
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for StateColorSequence<T> {
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
    impl<T: Deterministic> Observer<T> for StateColorSet<T> {
        type Current = Self;
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            let start = ts.state_color(state).unwrap();
            Self(math::Set::from_iter([start]))
        }
        fn current(&self) -> &Self::Current {
            &self
        }
        fn into_current(self) -> Self::Current {
            self
        }
        fn observe(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let t = ts.edge(state, sym)?;
            self.0.insert(ts.state_color(t.target()).unwrap());
            Some(t.target())
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for StateColorSet<T> {
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(Default::default(), |mut acc, x| {
                acc.0.extend(x.0.iter().cloned());
                acc
            })
        }
    }

    impl<T: Deterministic> Observer<T> for EdgeColorSet<T> {
        type Current = Self;
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(math::Set::default())
        }
        fn current(&self) -> &Self::Current {
            &self
        }
        fn into_current(self) -> Self::Current {
            self
        }
        fn observe(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let t = ts.edge(state, sym)?;
            self.0.insert(t.color());
            Some(t.target())
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for EdgeColorSet<T> {
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            Self(seq[time..].iter().fold(math::Set::default(), |mut acc, x| {
                acc.extend(x.0.iter().cloned());
                acc
            }))
        }
    }
    impl<T: Deterministic> Clone for EdgeColorSet<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    impl<T: Deterministic> Observer<T> for EdgeColorSequence<T> {
        type Current = Vec<EdgeColor<T>>;
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(vec![])
        }
        fn current(&self) -> &Self::Current {
            &self.0
        }
        fn into_current(self) -> Self::Current {
            self.0
        }
        fn observe(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let t = ts.edge(state, sym)?;
            self.0.push(t.color());
            Some(t.target())
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for EdgeColorSequence<T> {
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
        type Current = math::Set<(StateIndex<T>, SymbolOf<T>)>;

        fn current(&self) -> &Self::Current {
            &self.0
        }

        fn into_current(self) -> Self::Current {
            self.0
        }

        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(math::Set::default())
        }

        fn observe(
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
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            assert!(!seq.is_empty());
            assert!(time < seq.len());

            seq[time..].iter().fold(math::Set::default(), |mut acc, x| {
                acc.extend(x.iter().cloned());
                acc
            })
        }
    }
}
