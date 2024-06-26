use itertools::Itertools;

use crate::math::Map;

use crate::prelude::*;

use super::operations::MapEdgeColor;
use super::operations::MapEdges;
use super::operations::MapStateColor;
use super::operations::MatchingProduct;
use super::operations::ProductTransition;
use super::operations::RestrictByStateIndex;
use super::operations::StateIndexFilter;
use super::path::Lasso;
use super::Path;

pub type FiniteRunResult<A, Idx, Q, C> = Result<Path<A, Idx, Q, C>, Path<A, Idx, Q, C>>;
pub type OmegaRunResult<A, Idx, Q, C> = Result<Lasso<A, Idx, Q, C>, Path<A, Idx, Q, C>>;

/// A marker tait indicating that a [`TransitionSystem`] is deterministic, meaning for every state and
/// each possible input symbol from the alphabet, there is at most one transition. Under the hood, this
/// trait simply calls [`TransitionSystem::edges_from`] and checks whether there is at most one edge
/// for each symbol. If there is more than one edge, the methods of this trait panic.
pub trait Deterministic: TransitionSystem {
    /// Attempts to find the first edge that matches the given `matcher` from the given `state`. If no
    /// suitable transition exists, `None` is returned. If more than one edge matches the expression, the
    /// method panics.
    ///
    /// # Example
    /// ```
    /// use automata::prelude::*;
    /// let ts = TSBuilder::without_state_colors()
    ///     .with_transitions([(0, 'a', Void, 1), (1, 'a', Void, 2), (2, 'a', Void, 0)])
    ///     .into_right_congruence_bare(0);
    /// assert_eq!(ts.edge(0, &'a').unwrap().target(), 1);
    /// assert_eq!(ts.edge(1, &'a').unwrap().target(), 2);
    /// assert_eq!(ts.edge(2, &'a').unwrap().target(), 0);
    /// assert_eq!(ts.edge(0, &'b'), None);
    /// assert_eq!(ts.edge(3, &'a'), None);
    /// ```
    fn edge(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Self::EdgeRef<'_>> {
        if !self.contains_state_index(state) {
            return None;
        }
        let mut it = self
            .edges_from(state)?
            .filter(|e| matcher.matches(e.expression()));

        let first = it.next()?;
        debug_assert!(
            it.next().is_none(),
            "There should be only one edge with the given expression"
        );
        Some(first)
    }

    /// Returns just the [`TransitionSystem::StateIndex`] of the successor that is reached on the given `symbol`
    /// from `state`. If no suitable transition exists, `None` is returned.
    ///
    /// # Example
    /// ```
    /// use automata::prelude::*;
    ///
    /// let ts = TSBuilder::without_state_colors()
    ///     .with_transitions([(0, 'a', Void, 0), (0, 'b', Void, 1), (1, 'a', Void, 1), (1, 'b', Void, 1)])
    ///     .into_right_congruence_bare(0);
    /// assert_eq!(ts.successor_index(0, 'a'), Some(0));
    /// assert_eq!(ts.successor_index(0, 'b'), Some(1));
    /// assert_eq!(ts.successor_index(0, 'c'), None);
    /// ```
    fn successor_index(
        &self,
        state: StateIndex<Self>,
        symbol: SymbolOf<Self>,
    ) -> Option<Self::StateIndex> {
        if !self.contains_state_index(state) {
            return None;
        }
        self.edge(state, symbol).map(|t| t.target())
    }

    /// Returns the color of an edge starting in the given `state` and labeled with the given
    /// `expression`, if it exists. Otherwise, `None` is returned.
    fn edge_color(
        &self,
        state: StateIndex<Self>,
        expression: &EdgeExpression<Self>,
    ) -> Option<EdgeColor<Self>> {
        if !self.contains_state_index(state) {
            return None;
        }
        let mut symbols = expression.symbols();
        let sym = symbols.next().unwrap();
        assert_eq!(
            symbols.next(),
            None,
            "There are multiple symbols for this expression"
        );
        Some(self.edge(state, sym)?.color().clone())
    }

    /// Attempts to find the minimal representative of the indexed `state`, which the the length-lexicographically
    /// minimal word that can be used to reach `state`. If `state` is not reachable, `None` is returned.
    fn minimal_representative(&self, q: StateIndex<Self>) -> Option<MinimalRepresentative<Self>>
    where
        Self: Pointed,
    {
        self.minimal_representatives().find_map(|rep| {
            if rep.state_index() == q {
                Some(rep)
            } else {
                None
            }
        })
    }

    /// Gives an iterator over the minimal transition representatives, which are the length-lexicographically
    /// minimal words that can be used to use a transition. The iterator returns only unique elements.
    fn minimal_transition_representatives(&self) -> impl Iterator<Item = Vec<SymbolOf<Self>>>
    where
        Self: Pointed,
    {
        self.minimal_representatives()
            .flat_map(|rep| {
                self.symbols()
                    .map(move |a| word::Concat(&rep, [a]).collect_vec())
            })
            .unique()
    }

    /// Runs the given `word` on the transition system, starting from the initial state. The result is
    /// - [`Ok`] if the run is successful (i.e. for all symbols of `word` a suitable transition
    ///  can be taken),
    /// - [`Err`] if the run is unsuccessful, meaning a symbol is encountered for which no
    /// transition exists.
    ///
    /// It returns a [`crate::transition_system::path::PathIn`] in either case, which is a path in the transition system. So it is possible
    /// to inspect the path, e.g. to find out which state was reached or which transitions were taken.
    /// For more information, see [`crate::prelude::Path`].
    #[allow(clippy::type_complexity)]
    fn finite_run<W: FiniteWord<SymbolOf<Self>>>(
        &self,
        word: W,
    ) -> FiniteRunResult<Self::Alphabet, Self::StateIndex, Self::StateColor, Self::EdgeColor>
    where
        Self: Pointed,
    {
        self.finite_run_from(self.initial(), word)
    }

    /// Runs the given `word` on the transition system, starting from `state`. The result is
    /// - [`Ok`] if the run is successful (i.e. for all symbols of `word` a suitable transition
    ///  can be taken),
    /// - [`Err`] if the run is unsuccessful, meaning a symbol is encountered for which no
    /// transition exists.
    #[allow(clippy::type_complexity)]
    fn finite_run_from<W>(
        &self,
        origin: StateIndex<Self>,
        word: W,
    ) -> FiniteRunResult<Self::Alphabet, Self::StateIndex, Self::StateColor, Self::EdgeColor>
    where
        Self: Sized,
        W: FiniteWord<SymbolOf<Self>>,
    {
        let mut path = Path::empty_in_with_capacity(self, origin, word.len());
        for symbol in word.symbols() {
            if let Some(_o) = path.extend_in(&self, symbol) {
                continue;
            }
            return Err(path);
        }
        Ok(path)
    }

    /// Runs the given `word` from the `origin` state. If the run is successful, the function returns the indices
    /// of all states which appear infinitely often. For unsuccessful runs, `None` is returned.
    fn recurrent_state_indices_from<W: OmegaWord<SymbolOf<Self>>>(
        &self,
        origin: StateIndex<Self>,
        word: W,
    ) -> Option<impl Iterator<Item = Self::StateIndex>> {
        Some(
            self.omega_run_from(origin, word)
                .ok()?
                .into_recurrent_state_indices(),
        )
    }

    /// Returns an iterator over the state indices that are visited infinitely often when running the given `word`
    /// on the transition system, starting from the initial state. If the run is unsuccessful, `None` is returned.
    fn recurrent_state_indices<W: OmegaWord<SymbolOf<Self>>>(
        &self,
        word: W,
    ) -> Option<impl Iterator<Item = Self::StateIndex>>
    where
        Self: Pointed,
    {
        self.recurrent_state_indices_from(self.initial(), word)
    }

    /// Returns an iterator yielding the colors of states which are visited infinitely often when running the given `word`
    /// on the transition system, starting from the initial state. If the run is unsuccessful, `None` is returned.  
    fn recurrent_state_colors_from<W: OmegaWord<SymbolOf<Self>>>(
        &self,
        origin: StateIndex<Self>,
        word: W,
    ) -> Option<impl Iterator<Item = Self::StateColor>> {
        Some(
            self.omega_run_from(origin, word)
                .ok()?
                .into_recurrent_state_colors(),
        )
    }

    /// Returns an iterator yielding the colors of states which are visited infinitely often when running the given `word`
    /// on the transition system, starting from the initial state. If the run is unsuccessful, `None` is returned.
    fn recurrent_state_colors<W: OmegaWord<SymbolOf<Self>>>(
        &self,
        word: W,
    ) -> Option<impl Iterator<Item = Self::StateColor>>
    where
        Self: Pointed,
    {
        self.recurrent_state_colors_from(self.initial(), word)
    }

    /// Gives an iterator that emits the colors of edges which are taken infinitely often when running the given `word`
    /// on the transition system, starting from the initial state. If the run is unsuccessful, `None` is returned.
    fn recurrent_edge_colors_from<W>(
        &self,
        origin: StateIndex<Self>,
        word: W,
    ) -> Option<impl Iterator<Item = Self::EdgeColor>>
    where
        W: OmegaWord<SymbolOf<Self>>,
    {
        self.omega_run_from(origin, word)
            .ok()
            .map(|p| p.into_recurrent_edge_colors())
    }

    /// Gives an iterator that emits the colors of edges which are taken infinitely often when running the given `word`
    /// on the transition system, starting from the initial state. If the run is unsuccessful, `None` is returned.
    fn recurrent_edge_colors<W>(&self, word: W) -> Option<impl Iterator<Item = Self::EdgeColor>>
    where
        W: OmegaWord<SymbolOf<Self>>,
        Self: Pointed,
    {
        self.recurrent_edge_colors_from(self.initial(), word)
    }

    /// Returns a [`Vec`] containing the state indices that are visited when running the given `word`
    /// on the transition system, starting from the initial state. This may include states that are
    /// visited only finitely often. If the run is unsuccessful, `None` is returned.
    fn visited_state_sequence_from<W>(
        &self,
        origin: StateIndex<Self>,
        word: W,
    ) -> Option<Vec<Self::StateIndex>>
    where
        W: FiniteWord<SymbolOf<Self>>,
    {
        self.finite_run_from(origin, word)
            .ok()
            .map(|p| p.state_sequence().collect())
    }

    /// Returns a [`Vec`] containing the state indices that are visited when running the given `word`
    /// on the transition system, starting from the initial state. This may include states that are
    /// visited only finitely often. If the run is unsuccessful, `None` is returned.
    fn visited_state_sequence<W>(&self, word: W) -> Option<Vec<Self::StateIndex>>
    where
        W: FiniteWord<SymbolOf<Self>>,
        Self: Pointed,
    {
        self.visited_state_sequence_from(self.initial(), word)
    }

    /// Returns a [`Vec`] containing the state colors that are visited when running the given `word`
    /// on the transition system, starting from the initial state. This may include states that are
    /// visited only finitely often. If the run is unsuccessful, `None` is returned.
    fn visited_state_colors_from<W>(
        &self,
        origin: StateIndex<Self>,
        word: W,
    ) -> Option<Vec<Self::StateColor>>
    where
        W: FiniteWord<SymbolOf<Self>>,
    {
        self.finite_run_from(origin, word)
            .ok()
            .map(|p| p.state_colors().cloned().collect())
    }

    /// Returns a [`Vec`] containing the state colors that are visited when running the given `word`
    /// on the transition system, starting from the initial state. This may include states that are
    /// visited only finitely often. If the run is unsuccessful, `None` is returned.
    fn visited_state_colors<W>(&self, word: W) -> Option<Vec<Self::StateColor>>
    where
        W: FiniteWord<SymbolOf<Self>>,
        Self: Pointed,
    {
        self.visited_state_colors_from(self.initial(), word)
    }

    /// Returns a [`Vec`] containing the edge colors that are visited when running the given `word`
    /// on the transition system, starting from the initial state. This may include edges that are
    /// visited only finitely often. If the run is unsuccessful, `None` is returned.
    fn visited_edge_colors_from<W>(
        &self,
        origin: StateIndex<Self>,
        word: W,
    ) -> Option<Vec<Self::EdgeColor>>
    where
        W: FiniteWord<SymbolOf<Self>>,
    {
        self.finite_run_from(origin, word)
            .ok()
            .map(|p| p.edge_colors().cloned().collect())
    }

    /// Returns a [`Vec`] containing the edge colors that are visited when running the given `word`
    /// on the transition system, starting from the initial state. This may include edges that are
    /// visited only finitely often. If the run is unsuccessful, `None` is returned.
    fn visited_edge_colors<W>(&self, word: W) -> Option<Vec<Self::EdgeColor>>
    where
        W: FiniteWord<SymbolOf<Self>>,
        Self: Pointed,
    {
        self.visited_edge_colors_from(self.initial(), word)
    }

    /// Returns the color of the last edge that is taken when running the given `word` on the transition system,
    /// starting from the state indexed by `origin`. If the run is unsuccessful, `None` is returned.
    fn last_edge_color_from<W>(&self, origin: StateIndex<Self>, word: W) -> Option<Self::EdgeColor>
    where
        W: FiniteWord<SymbolOf<Self>>,
    {
        self.finite_run_from(origin, word)
            .ok()
            .and_then(|p| p.last_transition_color().cloned())
    }

    /// Returns the color of the last edge that is taken when running the given `word` on the transition system,
    /// starting from the initial state. If the run is unsuccessful, `None` is returned.
    fn last_edge_color<W>(&self, word: W) -> Option<Self::EdgeColor>
    where
        W: FiniteWord<SymbolOf<Self>>,
        Self: Pointed,
    {
        self.last_edge_color_from(self.initial(), word)
    }

    /// Runs the given `word` on the transition system, starting in the initial state.
    #[allow(clippy::type_complexity)]
    fn omega_run<W>(
        &self,
        word: W,
    ) -> OmegaRunResult<Self::Alphabet, Self::StateIndex, Self::StateColor, Self::EdgeColor>
    where
        W: OmegaWord<SymbolOf<Self>>,
        Self: Pointed,
    {
        self.omega_run_from(self.initial(), word)
    }

    /// Runs the given `word` on the transition system, starting from `state`.
    #[allow(clippy::type_complexity)]
    fn omega_run_from<W>(
        &self,
        origin: StateIndex<Self>,
        word: W,
    ) -> OmegaRunResult<Self::Alphabet, Self::StateIndex, Self::StateColor, Self::EdgeColor>
    where
        W: OmegaWord<SymbolOf<Self>>,
    {
        assert!(!word.cycle().is_empty(), "word must be infinite");

        let mut path = self.finite_run_from(origin, word.spoke())?;
        let mut position = path.len();
        let mut seen = Map::default();

        loop {
            match seen.insert(path.reached(), position) {
                Some(p) => {
                    return Ok(path.loop_back_to(p));
                }
                None => match self.finite_run_from(path.reached(), word.cycle()) {
                    Ok(p) => {
                        position += p.len();
                        path.extend_with(p);
                    }
                    Err(p) => {
                        path.extend_with(p);
                        return Err(path);
                    }
                },
            }
        }
    }

    /// Returns a string representation of the transition table of the transition system.
    fn build_transition_table<'a, SD, ED>(
        &'a self,
        state_decorator: SD,
        edge_decorator: ED,
    ) -> String
    where
        SD: Fn(Self::StateIndex, StateColor<Self>) -> String,
        ED: Fn(Self::EdgeRef<'a>) -> String,
    {
        let mut builder = tabled::builder::Builder::default();
        builder.push_record(
            std::iter::once("State".to_string())
                .chain(self.alphabet().universe().map(|s| format!("{:?}", s))),
        );
        for id in self.state_indices().sorted() {
            let mut row = vec![format!(
                "{}",
                state_decorator(
                    id,
                    self.state_color(id)
                        .expect("Every state should be colored!")
                )
            )];
            for sym in self.alphabet().universe() {
                if let Some(edge) = self.edge(id, sym) {
                    row.push(edge_decorator(edge));
                } else {
                    row.push("-".to_string());
                }
            }
            builder.push_record(row);
        }

        builder
            .build()
            .with(tabled::settings::Style::rounded())
            .to_string()
    }

    /// Returns the color of the state that is reached when running `word` from the state indexed by `from`.
    /// If the run is unsuccessful, `None` is returned.
    fn reached_state_color_from<W>(
        &self,
        from: StateIndex<Self>,
        word: W,
    ) -> Option<Self::StateColor>
    where
        W: FiniteWord<SymbolOf<Self>>,
    {
        self.finite_run_from(from, word)
            .ok()
            .map(|p| p.reached_state_color())
    }

    /// Returns the color of the state that is reached when running `word` from the initial state. If the run
    /// is unsuccessful, `None` is returned.
    fn reached_state_color<W>(&self, word: W) -> Option<Self::StateColor>
    where
        W: FiniteWord<SymbolOf<Self>>,
        Self: Pointed,
    {
        self.reached_state_color_from(self.initial(), word)
    }

    /// Returns the state that is reached by running the given `word` on the transition system,
    /// starting from the initial state. If the run is unsuccessful, `None` is returned.
    fn reached_state_index<W>(&self, word: W) -> Option<Self::StateIndex>
    where
        Self: Pointed,
        W: FiniteWord<SymbolOf<Self>>,
    {
        self.reached_state_index_from(self.initial(), word)
    }

    /// Tries to run the given `word` starting in the state indexed by `origin`. If
    /// no state is indexed, then `None` is immediately returned. Otherwise, the
    /// word is run and the index of the reached state is returned. If the run is
    /// unsuccessful, the function returns `None`.
    fn reached_state_index_from<W>(
        &self,
        origin: StateIndex<Self>,
        word: W,
    ) -> Option<Self::StateIndex>
    where
        Self: Sized,
        W: FiniteWord<SymbolOf<Self>>,
    {
        self.finite_run_from(origin, word).ok().map(|p| p.reached())
    }

    /// Returns true if `self` is accessible, meaning every state is reachable from the initial state.
    /// This is done by counting whether the number of minimal representatives matches the number of states.
    fn is_accessible(&self) -> bool
    where
        Self: Pointed,
    {
        self.size() == self.minimal_representatives().count()
    }

    /// Compute the escape prefixes of a set of omega words on a transition system.
    fn escape_prefixes<'a, W>(
        &self,
        words: impl Iterator<Item = &'a W>,
    ) -> impl Iterator<Item = String>
    where
        W: OmegaWord<SymbolOf<Self>> + 'a,
        Self: Pointed,
    {
        words
            .filter_map(|w| {
                self.omega_run(w)
                    .err()
                    .map(|path| w.prefix(path.len() + 1).as_string())
            })
            .unique()
    }
}

impl<D: Deterministic> Deterministic for &D {
    fn edge(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Self::EdgeRef<'_>> {
        D::edge(self, state, matcher)
    }
}

impl<D: Deterministic> Deterministic for &mut D {
    fn edge(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Self::EdgeRef<'_>> {
        D::edge(self, state, matcher)
    }
}

impl<L, R> Deterministic for MatchingProduct<L, R>
where
    L: Deterministic,
    R: Deterministic<Alphabet = L::Alphabet>,
    L::StateColor: Clone,
    R::StateColor: Clone,
{
    fn edge_color(
        &self,
        state: StateIndex<Self>,
        expression: &EdgeExpression<Self>,
    ) -> Option<EdgeColor<Self>> {
        let ProductIndex(l, r) = state;
        let left = self.0.edge_color(l, expression)?;
        let right = self.1.edge_color(r, expression)?;
        Some((left, right))
    }
    fn edge(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Self::EdgeRef<'_>> {
        let ProductIndex(l, r) = state;

        let ll = self.0.edge(l, &matcher)?;
        let rr = self.1.edge(r, matcher)?;
        Some(ProductTransition::new(
            ProductIndex(l, r),
            ll.expression(),
            (ll.color(), rr.color()),
            ProductIndex(ll.target(), rr.target()),
        ))
    }
}

impl<D, Ts, F> Deterministic for MapStateColor<Ts, F>
where
    D: Color,
    Ts: Deterministic,
    F: Fn(Ts::StateColor) -> D,
{
    fn edge(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Self::EdgeRef<'_>> {
        self.ts().edge(state, matcher)
    }
}

impl<D, Ts, F> Deterministic for MapEdgeColor<Ts, F>
where
    D: Color,
    Ts: Deterministic,
    F: Fn(Ts::EdgeColor) -> D,
{
}

impl<Ts: Deterministic, F> Deterministic for RestrictByStateIndex<Ts, F> where
    F: StateIndexFilter<Ts::StateIndex>
{
}

impl<Ts, D, F> Deterministic for MapEdges<Ts, F>
where
    Ts: Deterministic,
    D: Color,
    F: Fn(Ts::StateIndex, &EdgeExpression<Ts>, Ts::EdgeColor, Ts::StateIndex) -> D,
{
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;
    #[test]
    fn escape_prefixes() {
        // build set of words
        let words = [upw!("a"), upw!("a", "b"), upw!("b"), upw!("aa", "b")];

        // build transition system
        let ts = DTS::builder()
            .with_transitions([(0, 'a', Void, 1), (1, 'b', Void, 1)])
            .default_color(Void)
            .into_dts_with_initial(0);

        assert!(ts
            .escape_prefixes(words.iter())
            .eq(vec![String::from("aa"), String::from("b")].into_iter()));
    }
}
