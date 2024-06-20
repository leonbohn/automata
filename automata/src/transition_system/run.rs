#![allow(missing_docs)]
use std::marker::PhantomData;

use crate::prelude::*;

pub trait RunResult: Sized {
    /// The type of the state colors.
    type StateColor: Color;
    /// The type of the edge colors.
    type EdgeColor: Color;
    /// The type of the state indices.
    type StateIndex: IndexType;
    /// The type of symbol over which the input word operates.
    type Symbol: Symbol;
}

pub struct FiniteRun<'ts, T: TransitionSystem, W: Word<SymbolOf<T>>> {
    ts: &'ts T,
    start: StateIndex<T>,
    word: W,
}

impl<'ts, T: Deterministic, W: Word<SymbolOf<T>>> FiniteRun<'ts, T, W> {
    pub fn new(ts: &'ts T, start: StateIndex<T>, word: W) -> Self {
        Self { ts, start, word }
    }
    /// Evaluates the run. If successful, the reached state index is returned.
    /// If unsuccessful, the exit state and length of escape prefix is returned.
    pub fn evaluate(&self) -> Result<StateIndex<T>, (StateIndex<T>, usize)> {
        let mut taken = 0;
        let mut current = self.start;
        while let Some(sym) = self.word.nth(taken) {
            taken += 1;
            if let Some(next) = self.ts.successor_index(current, sym) {
                current = next;
            } else {
                return Err((current, taken));
            }
        }
        Ok(current)
    }
}

impl<'ts, T: TransitionSystem, W: Word<SymbolOf<T>>> RunResult for FiniteRun<'ts, T, W> {
    type StateColor = StateColor<T>;
    type EdgeColor = EdgeColor<T>;
    type StateIndex = StateIndex<T>;
    type Symbol = SymbolOf<T>;
}

impl<'ts, T: Deterministic, W: FiniteWord<SymbolOf<T>>> FiniteRunResult for FiniteRun<'ts, T, W> {
    fn state_colors(self) -> Option<impl Iterator<Item = Option<Self::StateColor>>> {
        if !self.ts.contains_state_index(self.start) {
            None
        } else {
            Some(FiniteRunner::<&T, W, OutputStateColor>::new(
                self.ts, self.word, self.start,
            ))
        }
    }

    fn edge_colors(self) -> Option<impl Iterator<Item = Option<Self::EdgeColor>>> {
        if !self.ts.contains_state_index(self.start) {
            None
        } else {
            Some(FiniteRunner::<&T, W, OutputEdgeColor>::new(
                self.ts, self.word, self.start,
            ))
        }
    }

    fn successful_indices(self) -> Option<impl Iterator<Item = Self::StateIndex>> {
        if !self.ts.contains_state_index(self.start) {
            None
        } else {
            Some(FiniteRunner::<&T, W, OutputStateIndex, true>::new(
                self.ts, self.word, self.start,
            ))
        }
    }

    fn indices(self) -> Option<impl Iterator<Item = Option<Self::StateIndex>>> {
        if !self.ts.contains_state_index(self.start) {
            None
        } else {
            Some(FiniteRunner::<&T, W, OutputStateIndex>::new(
                self.ts, self.word, self.start,
            ))
        }
    }

    fn successful(&self) -> bool {
        self.ts.contains_state_index(self.start)
            && FiniteRunner::<&T, &W, OutputStateIndex>::new(self.ts, &self.word, self.start)
                .all(|o| o.is_some())
    }
}

pub struct OutputStateIndex;
pub struct OutputStateColor;
pub struct OutputEdgeColor;
pub struct OutputReachedState;

pub struct FiniteRunner<
    T: Deterministic,
    W: FiniteWord<SymbolOf<T>>,
    X,
    const SUCCESSFUL: bool = false,
> {
    ts: T,
    word: W,
    state: Option<StateIndex<T>>,
    pos: usize,
    _phantom: PhantomData<X>,
}

impl<T: Deterministic, W: FiniteWord<SymbolOf<T>>, X, const SUCCESSFUL: bool>
    FiniteRunner<T, W, X, SUCCESSFUL>
{
    pub fn new(ts: T, word: W, state: StateIndex<T>) -> Self {
        Self {
            ts,
            word,
            state: Some(state),
            pos: 0,
            _phantom: PhantomData,
        }
    }
}

mod impl_iterators {
    use super::*;
    impl<T: Deterministic, W: FiniteWord<SymbolOf<T>>> Iterator
        for FiniteRunner<T, W, OutputStateIndex, false>
    {
        type Item = Option<StateIndex<T>>;
        fn next(&mut self) -> Option<Self::Item> {
            let out = self.state?;
            let Some(sym) = self.word.nth(self.pos) else {
                self.state = None;
                return Some(Some(out));
            };
            let Some(successor) = self.ts.successor_index(out, sym) else {
                return Some(None);
            };
            self.state = Some(successor);
            self.pos += 1;
            Some(Some(out))
        }
    }
    impl<T: Deterministic, W: FiniteWord<SymbolOf<T>>> Iterator
        for FiniteRunner<T, W, OutputStateIndex, true>
    {
        type Item = StateIndex<T>;
        fn next(&mut self) -> Option<Self::Item> {
            let out = self.state?;
            let Some(sym) = self.word.nth(self.pos) else {
                self.state = None;
                return Some(out);
            };
            let Some(successor) = self.ts.successor_index(out, sym) else {
                panic!("assumed successful run, but is not");
            };
            self.state = Some(successor);
            self.pos += 1;
            Some(out)
        }
    }

    impl<T: Deterministic, W: FiniteWord<SymbolOf<T>>> Iterator
        for FiniteRunner<T, W, OutputStateColor, false>
    {
        type Item = Option<StateColor<T>>;
        fn next(&mut self) -> Option<Self::Item> {
            let out = self
                .ts
                .state_color(self.state?)
                .expect("state should have a color");
            let Some(sym) = self.word.nth(self.pos) else {
                self.state = None;
                return Some(Some(out));
            };
            let Some(successor) = self.ts.successor_index(self.state.unwrap(), sym) else {
                return Some(None);
            };
            self.state = Some(successor);
            self.pos += 1;
            Some(Some(out))
        }
    }

    impl<T: Deterministic, W: FiniteWord<SymbolOf<T>>> Iterator
        for FiniteRunner<T, W, OutputEdgeColor, false>
    {
        type Item = Option<EdgeColor<T>>;
        fn next(&mut self) -> Option<Self::Item> {
            let q = self.state?;
            let sym = self.word.nth(self.pos)?;
            self.pos += 1;

            let Some(edge) = self.ts.edge(q, sym) else {
                return Some(None);
            };
            self.state = Some(edge.target());
            Some(Some(edge.color()))
        }
    }
}

/// A run is a sequence of states and edges that is consistent with the transition system.
/// Implementors of this trait represent such a run.
pub trait FiniteRunResult: RunResult {
    /// Returns an iterator over the state colors.
    fn state_colors(self) -> Option<impl Iterator<Item = Option<Self::StateColor>>>;
    /// Returns an iterator over the edge colors.
    fn edge_colors(self) -> Option<impl Iterator<Item = Option<Self::EdgeColor>>>;
    /// Returns an iterator over the state indices.
    fn indices(self) -> Option<impl Iterator<Item = Option<Self::StateIndex>>>;
    /// Returns whether the run is successful.
    fn successful(&self) -> bool;

    fn successful_indices(self) -> Option<impl Iterator<Item = Self::StateIndex>>;
    fn reached_index(self) -> Option<Self::StateIndex> {
        self.indices()?
            .last()
            .expect("at least origin state needs to be returned")
    }
    fn reached_color(self) -> Option<Self::StateColor> {
        self.state_colors()?.last()?
    }
    fn last_transition_color(self) -> Option<Self::EdgeColor> {
        self.edge_colors()?.last()?
    }
}

pub struct OmegaRun<'ts, T: Deterministic> {
    ts: &'ts T,
    word: ReducedOmegaWord<SymbolOf<T>>,
    origin: StateIndex<T>,
}

impl<'ts, T: Deterministic> RunResult for OmegaRun<'ts, T> {
    type StateColor = StateColor<T>;
    type EdgeColor = EdgeColor<T>;
    type StateIndex = StateIndex<T>;
    type Symbol = SymbolOf<T>;
}

impl<'ts, T: Deterministic> OmegaRun<'ts, T> {
    pub fn new(ts: &'ts T, origin: StateIndex<T>, word: ReducedOmegaWord<SymbolOf<T>>) -> Self {
        Self { ts, word, origin }
    }
    /// Executes the run. If successful, returns a triple (loop_start, loop_index, loop_length). If
    /// unsuccessful, returns a pair consisting of the exit state and the number of
    /// symbols needed to encounter a missing transition (i.e. the length of the
    /// escape prefix).
    pub fn evaluate(&self) -> Result<(StateIndex<T>, usize, usize), (StateIndex<T>, usize)> {
        let spoke = self.word.spoke();
        let current = self.ts.finite_run_from(self.origin, spoke).evaluate()?;
        let mut seen = math::Map::default();
        let mut iteration = 0;
        seen.insert(current, iteration);

        let cycle = self.word.cycle();
        loop {
            iteration += 1;
            match self.ts.finite_run_from(current, cycle).evaluate() {
                Ok(reached) => {
                    if let Some(&prev_iteration) = seen.get(&reached) {
                        let loop_index = spoke.len() + prev_iteration * cycle.len();
                        let loop_length = (iteration - prev_iteration) * cycle.len();
                        return Ok((reached, loop_index, loop_length));
                    }
                }
                Err((reached, len)) => {
                    return Err((reached, spoke.len() + cycle.len() * (iteration - 1) + len))
                }
            }
        }
    }
}

impl<'ts, T: Deterministic> OmegaRunResult for OmegaRun<'ts, T> {
    fn recurring_state_colors_iter(self) -> Option<impl Iterator<Item = Self::StateColor>> {
        Some(std::iter::empty())
    }

    fn recurring_edge_colors_iter(self) -> Option<impl Iterator<Item = Self::EdgeColor>> {
        Some(std::iter::empty())
    }

    fn recurring_state_indices_iter(self) -> Option<impl Iterator<Item = Self::StateIndex>> {
        let spoke = self.word.spoke();
        let current = self.ts.reached_state_index_from(self.origin, spoke)?;
        let mut seen = math::Set::default();
        let mut iteration = 0;
        seen.insert(current);

        let cycle = self.word.cycle();
        while let Some(reached) = self.ts.reached_state_index_from(current, cycle) {
            iteration += 1;
            if !seen.insert(reached) {
                let repeated = cycle.repeat(iteration);
                let cycle_run = self
                    .ts
                    .finite_run_from(reached, repeated)
                    .successful_indices();
                return Some(cycle_run.expect("run should be successful!"));
            }
        }

        None
    }

    fn escape_prefix(self) -> Option<Vec<Self::Symbol>> {
        todo!()
    }
}

/// A run is a sequence of states and edges that is consistent with the transition system.
/// Implementors of this trait represent an infinite run.
pub trait OmegaRunResult: RunResult {
    /// Returns an iterator over the state colors.
    fn recurring_state_colors_iter(self) -> Option<impl Iterator<Item = Self::StateColor>>;
    /// Returns an iterator over the edge colors.
    fn recurring_edge_colors_iter(self) -> Option<impl Iterator<Item = Self::EdgeColor>>;
    /// Returns an iterator over the state indices.
    fn recurring_state_indices_iter(self) -> Option<impl Iterator<Item = Self::StateIndex>>;
    fn escape_prefix(self) -> Option<Vec<Self::Symbol>>;
}
