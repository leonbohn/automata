use super::AccessWords;
use super::operations::MatchingProduct;
use super::operations::ProductIndex;
use super::operations::RestrictByStateIndex;
use super::operations::StateIndexFilter;
use super::run::Run;
use crate::congruence::MinimalRepresentative;
use crate::ts::{EdgeColor, EdgeExpression, EdgeOf, EdgeRef, StateColor, StateIndex, SymbolOf};
use crate::{Pointed, States, TransitionSystem};
use crate::{
    alphabet::{Alphabet, Expression},
    word,
    word::{FiniteWord, Word},
};
use itertools::Itertools;

/// Marks a [`TransitionSystem`] as deterministic: for every state and every symbol of the alphabet there is
/// at most one edge. This is guaranteed by construction (or by a checked wrapper), not verified at runtime.
///
/// The required method is [`Deterministic::edge`]. Storages implement it, together with
/// [`TransitionSystem::edges_from`], directly. Lazy views implement `edge` and derive `edges_from`
/// from it with [`DeterministicEdgesFrom`](crate::ts::DeterministicEdgesFrom). No provided method of this trait calls
/// [`TransitionSystem::edges_from`], so a view cannot recurse between the two.
pub trait Deterministic: TransitionSystem {
    /// Returns the edge leaving `state` that is taken on `symbol`, or `None` if there is no such edge
    /// or `state` does not exist.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     Void,
    ///     ts::{Deterministic, Builder},
    /// };
    ///
    /// let ts = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', Void, 1), (1, 'a', Void, 2), (2, 'a', Void, 0)])
    ///     .into_right_congruence(0);
    /// assert_eq!(ts.edge(0, 'a').unwrap().target(), 1);
    /// assert_eq!(ts.edge(1, 'a').unwrap().target(), 2);
    /// assert_eq!(ts.edge(2, 'a').unwrap().target(), 0);
    /// assert_eq!(ts.edge(0, 'b'), None);
    /// assert_eq!(ts.edge(3, 'a'), None);
    /// ```
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>>;

    /// Returns the target of the edge leaving `state` on `symbol`, if it exists.
    fn successor(
        &self,
        state: StateIndex<Self>,
        symbol: SymbolOf<Self>,
    ) -> Option<Self::StateIndex> {
        self.edge(state, symbol).map(|t| t.target())
    }

    /// Folds the given finite word in `self` staring from the `source`.
    ///
    /// For each taken transition, `func` is applied to an accumulated value
    /// which is initialized with the given `init`.
    ///
    /// If no transition can be taken, `bail` is called on the currently
    /// accumulated value with the state and symbol that are problematic.
    fn fold_finite_from<X, Y, W, F, G>(
        &self,
        source: StateIndex<Self>,
        init: X,
        word: W,
        func: F,
        bail: G,
    ) -> Result<X, Y>
    where
        W: AsRef<[SymbolOf<Self>]>,
        F: Fn(&Self, &mut X, EdgeOf<'_, Self>),
        G: Fn(&Self, X, StateIndex<Self>, SymbolOf<Self>) -> Y,
    {
        let mut current_state = source;
        let mut current_x = init;
        for sym in word.as_ref() {
            let Some(e) = self.edge(current_state, *sym) else {
                return Err((bail)(self, current_x, current_state, *sym));
            };
            current_state = e.target();
            (func)(self, &mut current_x, e);
        }
        Ok(current_x)
    }

    /// Returns true if on the given state, the word is a loop.
    fn is_loop_on<W: FiniteWord<Symbol = SymbolOf<Self>>>(
        &self,
        state: StateIndex<Self>,
        word: W,
    ) -> bool {
        Some(state) == self.reached_state_from(state, word)
    }

    /// Returns the color of an edge starting in the given `state` and labeled with the given
    /// `expression`, if it exists. Otherwise, `None` is returned. This includes expressions
    /// that match no symbol or more than one symbol.
    fn edge_color(
        &self,
        state: StateIndex<Self>,
        expression: &EdgeExpression<Self>,
    ) -> Option<EdgeColor<Self>> {
        let mut symbols = expression.symbols();
        let sym = symbols.next()?;
        if symbols.next().is_some() {
            // the expression stands for several transitions, which may have different colors
            return None;
        }
        Some(self.edge(state, sym)?.color().clone())
    }

    /// Attempts to find the minimal representative of the indexed `state`, which the the length-lexicographically
    /// minimal word that can be used to reach `state`. If `state` is not reachable, `None` is returned.
    fn minimal_representative(&self, q: StateIndex<Self>) -> Option<MinimalRepresentative<Self>>
    where
        Self: Pointed,
    {
        AccessWords::new(self, self.initial())
            .word_to(q)
            .map(|word| MinimalRepresentative::new(word, q))
    }

    /// Gives an iterator over the minimal transition representatives, which are the length-lexicographically
    /// minimal words that can be used to use a transition. The iterator returns only unique elements.
    fn minimal_transition_representatives(&self) -> impl Iterator<Item = Vec<SymbolOf<Self>>>
    where
        Self: Pointed,
    {
        self.minimal_representatives_iter()
            .flat_map(|rep| {
                self.symbols()
                    .map(move |a| word::Concat(&rep, [a]).collect_vec())
            })
            .unique()
    }

    /// Creates the [`Run`] of `word` on the transition system, starting in the initial state. Call
    /// one of its methods to execute it, e.g. [`Run::reached_state`] or [`Run::observe`]. For finite
    /// and for infinite words alike, a run that takes a symbol for which there is no transition
    /// escapes the transition system.
    #[inline(always)]
    fn run<W: Word<Symbol = SymbolOf<Self>>>(&self, word: W) -> Run<'_, Self, W>
    where
        Self: Pointed + Sized,
    {
        Run::new(self, self.initial(), word)
    }

    /// Creates the [`Run`] of `word` on the transition system, starting in the state `start`.
    #[inline(always)]
    fn run_from<W: Word<Symbol = SymbolOf<Self>>>(
        &self,
        start: StateIndex<Self>,
        word: W,
    ) -> Run<'_, Self, W>
    where
        Self: Sized,
    {
        Run::new(self, start, word)
    }

    /// Returns the state that is reached by running the finite `word`, starting from the initial
    /// state. If the run escapes the transition system, `None` is returned.
    #[inline(always)]
    fn reached_state<W>(&self, word: W) -> Option<StateIndex<Self>>
    where
        Self: Pointed + Sized,
        W: FiniteWord<Symbol = SymbolOf<Self>>,
    {
        self.run(word).reached_state()
    }

    /// Returns the state that is reached by running the finite `word`, starting from `origin`. If
    /// the run escapes the transition system, `None` is returned.
    #[inline(always)]
    fn reached_state_from<W>(&self, origin: StateIndex<Self>, word: W) -> Option<StateIndex<Self>>
    where
        Self: Sized,
        W: FiniteWord<Symbol = SymbolOf<Self>>,
    {
        self.run_from(origin, word).reached_state()
    }

    /// Returns a string representation of the transition table of the transition system, with
    /// one row for each of the given `states` (in ascending order).
    fn build_transition_table<'a, SD, ED>(
        &'a self,
        states: impl IntoIterator<Item = Self::StateIndex>,
        state_decorator: SD,
        edge_decorator: ED,
    ) -> String
    where
        SD: Fn(Self::StateIndex, StateColor<Self>) -> String,
        ED: Fn(EdgeOf<'a, Self>) -> String,
    {
        let mut builder = tabled::builder::Builder::default();
        builder.push_record(
            std::iter::once("State".to_string())
                .chain(self.alphabet().universe().map(|s| format!("{:?}", s))),
        );
        for id in states.into_iter().sorted() {
            let Some(color) = self.state_color(id) else {
                continue;
            };
            let mut row = vec![state_decorator(id, color.into_owned()).to_string()];
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

    /// Returns true if `self` is accessible, meaning every state is reachable from the initial state.
    /// This is done by counting whether the number of minimal representatives matches the number of states.
    fn is_accessible(&self) -> bool
    where
        Self: Pointed + States,
    {
        self.state_count() == self.reachable_state_indices().count()
    }
}

impl<D: Deterministic> Deterministic for &D {
    #[inline(always)]
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        D::edge(self, state, symbol)
    }
}

impl<D: Deterministic> Deterministic for &mut D {
    #[inline(always)]
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        D::edge(self, state, symbol)
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
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        let ProductIndex(l, r) = state;

        let ll = self.0.edge(l, symbol)?;
        let rr = self.1.edge(r, symbol)?;
        Some(EdgeRef::owned(
            ProductIndex(l, r),
            ll.expression(),
            (ll.color().clone(), rr.color().clone()),
            ProductIndex(ll.target(), rr.target()),
        ))
    }
}

impl<Ts: Deterministic, F> Deterministic for RestrictByStateIndex<Ts, F>
where
    F: StateIndexFilter<Ts::StateIndex>,
{
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        if !self.filter().is_unmasked(state) {
            return None;
        }
        self.ts()
            .edge(state, symbol)
            .filter(|e| self.filter().is_unmasked(e.target()))
    }
}

#[cfg(test)]
mod tests {
    use crate::DTS;
    use crate::Void;
    use crate::ts::Deterministic;

    #[test]
    fn escape_prefixes() {
        // build set of words
        let words = [upw!("a"), upw!("a", "b"), upw!("b"), upw!("aa", "b")];

        // build transition system
        let ts = DTS::builder()
            .with_transitions([(0, 'a', Void, 1), (1, 'b', Void, 1)])
            .default_color(Void)
            .into_dts_with_initial(0);

        assert!(ts.run(upw!("b")).escape_prefix().is_some());
        assert!(ts.run(upw!("b", "a")).escape_prefix().is_some());
        assert!(ts.run(upw!("a", "b")).escape_prefix().is_none());
        // a^ω and aab^ω both escape after the prefix `aa`, which counts only once
        let distinct: std::collections::HashSet<_> = words
            .iter()
            .filter_map(|w| ts.run(w).escape_prefix())
            .collect();
        assert_eq!(distinct.len(), 2);
    }

    #[test]
    fn equal_escape_prefixes_hash_equally() {
        use std::hash::{DefaultHasher, Hash, Hasher};

        let ts = DTS::builder()
            .with_transitions([(0, 'a', Void, 1), (1, 'b', Void, 1)])
            .default_color(Void)
            .into_dts_with_initial(0);
        let first = ts.run(upw!("a")).escape_prefix().unwrap();
        let second = ts.run(upw!("aa", "b")).escape_prefix().unwrap();
        assert_eq!(first, second);
        let hash = |p: &crate::ts::run::EscapePrefix<_>| {
            let mut hasher = DefaultHasher::new();
            p.hash(&mut hasher);
            hasher.finish()
        };
        assert_eq!(hash(&first), hash(&second));
    }
}
