use std::{cell::OnceCell, marker::PhantomData};

use crate::prelude::*;

pub struct FiniteRun<'ts, T: TransitionSystem, W: Word<SymbolOf<T>>> {
    ts: &'ts T,
    start: StateIndex<T>,
    word: W,
}

impl<'ts, T: TransitionSystem, W: Word<SymbolOf<T>>> FiniteRun<'ts, T, W> {
    pub fn new(ts: &'ts T, start: StateIndex<T>, word: W) -> Self {
        Self { ts, start, word }
    }
}

impl<'ts, T: Deterministic, W: FiniteWord<SymbolOf<T>>> FiniteRunResult for FiniteRun<'ts, T, W> {
    type StateColor = StateColor<T>;

    type EdgeColor = EdgeColor<T>;

    type StateIndex = StateIndex<T>;

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

pub struct FiniteRunner<T: Deterministic, W: FiniteWord<SymbolOf<T>>, X> {
    ts: T,
    word: W,
    state: Option<StateIndex<T>>,
    pos: usize,
    _phantom: PhantomData<X>,
}

impl<T: Deterministic, W: FiniteWord<SymbolOf<T>>, X> FiniteRunner<T, W, X> {
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
        for FiniteRunner<T, W, OutputStateIndex>
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
        for FiniteRunner<T, W, OutputStateColor>
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
        for FiniteRunner<T, W, OutputEdgeColor>
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
pub trait FiniteRunResult: Sized {
    /// The type of the state colors.
    type StateColor;
    /// The type of the edge colors.
    type EdgeColor;
    /// The type of the state indices.
    type StateIndex: IndexType;
    /// Returns an iterator over the state colors.
    fn state_colors(self) -> Option<impl Iterator<Item = Option<Self::StateColor>>>;
    /// Returns an iterator over the edge colors.
    fn edge_colors(self) -> Option<impl Iterator<Item = Option<Self::EdgeColor>>>;
    /// Returns an iterator over the state indices.
    fn indices(self) -> Option<impl Iterator<Item = Option<Self::StateIndex>>>;
    /// Returns whether the run is successful.
    fn successful(&self) -> bool;
    fn reached_index(self) -> Option<Self::StateIndex> {
        self.indices()?
            .last()
            .expect("at least origin state needs to be returned")
    }
}

pub struct OmegaRun<'ts, T: Deterministic> {
    ts: &'ts T,
    word: ReducedOmegaWord<SymbolOf<T>>,
    origin: StateIndex<T>,
}

impl<'ts, T: Deterministic> OmegaRun<'ts, T> {
    pub fn new(ts: &'ts T, origin: StateIndex<T>, word: ReducedOmegaWord<SymbolOf<T>>) -> Self {
        Self { ts, word, origin }
    }
}

impl<'ts, T: Deterministic> OmegaRunResult for OmegaRun<'ts, T> {
    type StateColor = StateColor<T>;

    type EdgeColor = EdgeColor<T>;

    type StateIndex = StateIndex<T>;

    fn recurring_state_colors_iter(self) -> Option<impl Iterator<Item = Self::StateColor>> {
        Some(std::iter::empty())
    }

    fn recurring_edge_colors_iter(self) -> Option<impl Iterator<Item = Self::EdgeColor>> {
        Some(std::iter::empty())
    }

    fn recurring_state_indices_iter(self) -> Option<impl Iterator<Item = Self::StateIndex>> {
        let word = self.word;
        let current = self
            .ts
            .finite_run_from(self.origin, word.spoke())
            .reached_index()?;
        let mut position = word.spoke_length();
        let mut seen = math::Set::default();
        let mut iteration = 0;
        seen.insert(current);

        while let Some(reached) = self
            .ts
            .finite_run_from(current, word.cycle())
            .reached_index()
        {
            iteration += 1;
            if !seen.insert(reached) {
                return Some(
                    self.ts.finite_run_from(
                        reached,
                        word.cycle()
                            .symbols()
                            .cycle(iteration)
                            .take(iteration * word.cycle_length()),
                    ),
                );
            }
        }
        None
    }
}

/// A run is a sequence of states and edges that is consistent with the transition system.
/// Implementors of this trait represent an infinite run.
pub trait OmegaRunResult {
    /// The type of the state colors.
    type StateColor;
    /// The type of the edge colors.
    type EdgeColor;
    /// The type of the state indices.
    type StateIndex: IndexType;
    /// Returns an iterator over the state colors.
    fn recurring_state_colors_iter(self) -> Option<impl Iterator<Item = Self::StateColor>>;
    /// Returns an iterator over the edge colors.
    fn recurring_edge_colors_iter(self) -> Option<impl Iterator<Item = Self::EdgeColor>>;
    /// Returns an iterator over the state indices.
    fn recurring_state_indices_iter(self) -> Option<impl Iterator<Item = Self::StateIndex>>;
}
