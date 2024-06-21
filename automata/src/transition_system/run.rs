#![allow(missing_docs)]
use std::marker::PhantomData;

use crate::prelude::*;

pub trait FiniteObserver<T: TransitionSystem>: Sized {
    type Output;
    fn current(&self) -> &Self::Output;
    fn begin(ts: &T, state: StateIndex<T>) -> Self;
    fn observe(&mut self, ts: &T, state: StateIndex<T>, sym: SymbolOf<T>) -> Option<StateIndex<T>>;
}

#[derive(Debug, Clone, Copy)]
pub struct NoObserver;
impl<T: Deterministic> FiniteObserver<T> for NoObserver {
    type Output = ();
    fn current(&self) -> &Self::Output {
        &()
    }
    fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
        NoObserver
    }
    fn observe(&mut self, ts: &T, state: StateIndex<T>, sym: SymbolOf<T>) -> Option<StateIndex<T>> {
        ts.successor_index(state, sym)
    }
}

pub struct ReachedState<Idx>(Idx);
impl<T: Deterministic> FiniteObserver<T> for ReachedState<StateIndex<T>> {
    type Output = StateIndex<T>;
    fn current(&self) -> &Self::Output {
        &self.0
    }
    fn begin(_ts: &T, state: StateIndex<T>) -> Self {
        Self(state)
    }
    fn observe(&mut self, ts: &T, state: StateIndex<T>, sym: SymbolOf<T>) -> Option<StateIndex<T>> {
        self.0 = ts.successor_index(state, sym)?;
        Some(self.0)
    }
}
pub struct ReachedColor<Q>(Q);
impl<T: Deterministic> FiniteObserver<T> for ReachedColor<StateColor<T>> {
    type Output = StateColor<T>;
    fn current(&self) -> &Self::Output {
        &self.0
    }
    fn begin(ts: &T, state: StateIndex<T>) -> Self {
        Self(ts.state_color(state).unwrap())
    }
    fn observe(&mut self, ts: &T, state: StateIndex<T>, sym: SymbolOf<T>) -> Option<StateIndex<T>> {
        let succ = ts.successor_index(state, sym)?;
        self.0 = ts.state_color(succ).unwrap();
        Some(succ)
    }
}

pub struct LeastStateColor<Q>(Q);
impl<T: Deterministic> FiniteObserver<T> for LeastStateColor<StateColor<T>> {
    type Output = StateColor<T>;
    fn current(&self) -> &Self::Output {
        &self.0
    }
    fn begin(ts: &T, state: StateIndex<T>) -> Self {
        Self(ts.state_color(state).unwrap())
    }
    fn observe(&mut self, ts: &T, state: StateIndex<T>, sym: SymbolOf<T>) -> Option<StateIndex<T>> {
        let succ = ts.successor_index(state, sym)?;
        self.0 = std::cmp::min(ts.state_color(succ).unwrap(), self.0);
        Some(succ)
    }
}
impl<T: Deterministic> InfiniteObserver<T> for LeastStateColor<StateColor<T>>
where
    StateColor<T>: Default + Ord,
{
    fn loop_back(seq: &[Self::Output], ts: &T, time: usize) -> Self::Output {
        seq[time..].iter().min()
    }
}

pub struct LeastEdgeColor<C>(C);
impl<T: Deterministic> FiniteObserver<T> for LeastEdgeColor<EdgeColor<T>>
where
    EdgeColor<T>: Default,
{
    type Output = EdgeColor<T>;
    fn current(&self) -> &Self::Output {
        &self.0
    }
    fn begin(ts: &T, state: StateIndex<T>) -> Self {
        Self(Default::default())
    }
    fn observe(&mut self, ts: &T, state: StateIndex<T>, sym: SymbolOf<T>) -> Option<StateIndex<T>> {
        let e = ts.transition(state, sym)?;
        self.0 = std::cmp::min(e.color(), self.0);
        Some(e.target())
    }
}
impl<T: Deterministic> InfiniteObserver<T> for LeastEdgeColor<EdgeColor<T>>
where
    EdgeColor<T>: Default + Ord,
{
    fn loop_back(seq: &[Self::Output], ts: &T, time: usize) -> Self::Output {
        seq[time..].iter().min()
    }
}

pub struct StateSet<T: TransitionSystem>(math::Set<StateIndex<T>>);
impl<T: Deterministic> FiniteObserver<T> for StateSet<T> {
    type Output = Self;
    fn begin(ts: &T, state: StateIndex<T>) -> Self {
        Self(math::Set::from_iter([state]))
    }
    fn current(&self) -> &Self::Output {
        &self.0
    }
    fn observe(&mut self, ts: &T, state: StateIndex<T>, sym: SymbolOf<T>) -> Option<StateIndex<T>> {
        let successor_index = ts.successor_index(state, sym)?;
        self.0.push(successor_index);
        Some(successor_index)
    }
}
impl<T: Deterministic> InfiniteObserver<T> for StateSet<T> {
    fn loop_back(seq: &[Self::Output], ts: &T, time: usize) -> Self::Output {
        seq[time..].iter().fold(math::Set::default(), |acc, x| {
            acc.extend(x);
            acc
        })
    }
}
pub struct StateColorSet<T: TransitionSystem>(math::Set<StateColor<T>>);
impl<T: Deterministic> FiniteObserver<T> for StateColorSet<T> {
    type Output = Self;
    fn begin(ts: &T, state: StateIndex<T>) -> Self {
        let start = ts.state_color(state).unwrap();
        Self(math::Set::from_iter([start]))
    }
    fn current(&self) -> &Self::Output {
        &self.0
    }
    fn observe(&mut self, ts: &T, state: StateIndex<T>, sym: SymbolOf<T>) -> Option<StateIndex<T>> {
        let t = ts.transition(state, sym)?;
        self.0.push(t.color());
        Some(t.target())
    }
}
impl<T: Deterministic> InfiniteObserver<T> for StateColorSet<T> {
    fn loop_back(seq: &[Self::Output], ts: &T, time: usize) -> Self::Output {
        seq[time..].iter().fold(math::Set::default(), |acc, x| {
            acc.extend(x);
            acc
        })
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

pub struct Run<
    'ts,
    T: Deterministic,
    W: Word<SymbolOf<T>>,
    const FINITE: bool,
    O: FiniteObserver<T> = NoObserver,
> {
    ts: &'ts T,
    start: StateIndex<T>,
    word: W,
    observer: PhantomData<O>,
}

pub struct EscapePrefix<W> {
    word: W,
    length: usize,
}

impl<W> EscapePrefix<W> {
    pub fn new(word: W, length: usize) -> Self {
        Self { word, length }
    }
    pub fn with_word<V>(self, word: V) -> EscapePrefix<V> {
        EscapePrefix {
            word,
            length: self.length,
        }
    }
    pub fn with_length(self, len: usize) -> Self {
        Self {
            word: self.word,
            length: len,
        }
    }
}

pub enum FiniteRunOutput<T: TransitionSystem, W: Word<SymbolOf<T>>, O: FiniteObserver<T>> {
    Reached(StateIndex<T>, O::Output),
    Failed(StateIndex<T>, EscapePrefix<W>),
}

impl<T: TransitionSystem, W: Word<SymbolOf<T>>, O: FiniteObserver<T>> FiniteRunOutput<T, W, O> {
    fn escape_state(&self) -> Option<StateIndex<T>> {
        match self {
            FiniteRunOutput::Reached(_, _) => None,
            FiniteRunOutput::Failed(state, _) => Some(*state),
        }
    }
    fn escape_prefix(&self) -> Option<&EscapePrefix<W>> {
        match self {
            FiniteRunOutput::Reached(_, _) => None,
            FiniteRunOutput::Failed(_state, ep) => Some(ep),
        }
    }
    fn into_reached_state(self) -> Option<StateIndex<T>> {
        match self {
            FiniteRunOutput::Reached(r, _) => Some(r),
            _ => None,
        }
    }
    fn into_output(self) -> Option<O::Output> {
        match self {
            FiniteRunOutput::Reached(_, o) => Some(o),
            _ => None,
        }
    }
}

pub enum InfiniteRunOutput<T: TransitionSystem, W: OmegaWord<SymbolOf<T>>, O: InfiniteObserver<T>> {
    Successful(O::Output),
    Failed(StateIndex<T>, EscapePrefix<W>),
}

impl<T: TransitionSystem, W: OmegaWord<SymbolOf<T>>, O: InfiniteObserver<T>>
    InfiniteRunOutput<T, W, O>
{
    pub fn into_output(self) -> Option<O::Output> {
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

impl<'ts, T: Deterministic, W: Word<SymbolOf<T>>, const FINITE: bool, O: FiniteObserver<T>>
    RunResult for Run<'ts, T, W, FINITE, O>
{
    type StateColor = StateColor<T>;
    type EdgeColor = EdgeColor<T>;
    type StateIndex = StateIndex<T>;
    type Symbol = SymbolOf<T>;
}

impl<'ts, T: Deterministic, W: FiniteWord<SymbolOf<T>>, O: FiniteObserver<T>>
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
            taken += 1;
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
        }
        FiniteRunOutput::Reached(current, observer.current())
    }
}

pub trait InfiniteObserver<T: TransitionSystem>: FiniteObserver<T> {
    fn loop_back(seq: &[Self::Output], ts: &T, time: usize) -> Self::Output;
}
impl<T: Deterministic> InfiniteObserver<T> for NoObserver {
    fn loop_back(_seq: &[Self::Output], _ts: &T, _time: usize) -> Self::Output {}
}

impl<'ts, T: Deterministic, W: OmegaWord<SymbolOf<T>>, O: InfiniteObserver<T>>
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
    pub fn evaluate(&self) -> InfiniteRunOutput<T, &W, O> {
        let spoke = self.word.spoke();
        // first evaluate the finite run piece
        let mut current = match self.ts.finite_run_from::<_, O>(self.start, spoke) {
            FiniteRunOutput::Reached(r, _) => r,
            FiniteRunOutput::Failed(state, ep) => {
                return InfiniteRunOutput::Failed(state, ep.with_word(&self.word))
            }
        };

        let mut seen = math::Map::default();
        let mut iteration = 0;
        seen.insert(current, iteration);
        let mut seq = vec![];

        let cycle = self.word.cycle();
        loop {
            iteration += 1;
            match self.ts.finite_run_from::<_, O>(current, &cycle) {
                FiniteRunOutput::Reached(reached, output) => {
                    if let Some(&prev_iteration) = seen.get(&reached) {
                        return InfiniteRunOutput::Successful(O::loop_back(
                            &seq,
                            self.ts,
                            prev_iteration,
                        ));
                    }
                    seq.push(output)
                }
                FiniteRunOutput::Failed(reached, ep) => {
                    return InfiniteRunOutput::Failed(
                        reached,
                        EscapePrefix {
                            word: &self.word,
                            length: self.word.spoke_length()
                                + cycle.len() * (iteration - 1)
                                + ep.length,
                        },
                    )
                }
            }
        }
    }
}
