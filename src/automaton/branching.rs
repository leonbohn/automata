//! The branching of automata. An acceptance condition like [`super::BuchiCondition`] says which
//! runs are accepting. On its own it is the [`Semantics`] of a deterministic automaton, which has
//! one run per word. Wrapped in [`Existential`], a word is accepted if *some* of its runs is
//! accepting, which works on any [`TransitionSystem`].
//!
//! Wrapping works for every condition that implements [`CycleCondition`] (infinite words) or
//! [`FinalStateCondition`] (finite words), so each nondeterministic automaton type is just an
//! alias, see [`super::NFA`], [`super::NBA`], [`super::NCW`], [`super::NPA`], [`super::NRA`] and
//! [`super::NMA`].

use super::Semantics;
use crate::alphabet::{Expression, Matcher};
use crate::math;
use crate::ts::connected_components::Scc;
use crate::ts::operations::ProductIndex;
use crate::ts::{
    EdgeColor, EdgeExpression, EdgeOf, EdgeRef, Sccs, StateColor, StateIndex, SymbolOf,
};
use crate::word::{Finite, FiniteWord, Omega, OmegaWord, Word};
use crate::{Color, TransitionSystem};
use std::borrow::Cow;
use std::hash::Hash;

/// An acceptance condition on the set of edge colors that a run sees infinitely often. This is
/// what [`Existential`] needs to decide whether some run on an infinite word is accepting, and what
/// [`super::Emptiness`] needs to find an accepted word.
///
/// Some run is accepting if and only if there is a cycle whose set of edge colors satisfies the
/// condition. Such a cycle is searched by decomposing into strongly connected components: if the
/// colors of a whole component satisfy the condition, a cycle through all of them exists. If they
/// do not, a good cycle in the component has to avoid some colors, and [`Self::avoid`] says which.
pub trait CycleCondition {
    /// The type of the edge colors that the condition looks at.
    type Color: Color + Hash + Eq;

    /// Returns true if a run that sees exactly the edge colors in `colors` infinitely often is
    /// accepting.
    fn satisfied_by(&self, colors: &math::FxIndexSet<Self::Color>) -> bool;

    /// Called for the colors of a strongly connected component that do not satisfy the condition.
    /// Returns the alternatives for a cycle in that component that does satisfy it: each is a set
    /// of colors that such a cycle avoids, and every good cycle avoids at least one of them. No
    /// alternative means the component has no good cycle.
    ///
    /// The default tries leaving out each color in turn, which is correct for every condition but
    /// exponential in the number of colors. Conditions with more structure override it, a parity
    /// condition for example only has to avoid the decisive priority.
    fn avoid(&self, colors: &math::FxIndexSet<Self::Color>) -> Vec<Vec<Self::Color>> {
        colors.iter().map(|color| vec![color.clone()]).collect()
    }
}

/// An acceptance condition of finite words that only looks at the color of the state that is
/// reached, like [`super::ReachabilityCondition`]. [`Existential`] uses it for automata over finite
/// words.
pub trait FinalStateCondition {
    /// The type of the state colors that the condition looks at.
    type StateColor;
    /// Returns true if a run that ends in a state with the given color is accepting.
    fn accepts_final(&self, color: &Self::StateColor) -> bool;
}

/// Accepts a word if some run on it satisfies the acceptance condition `C`. These are the
/// [`Semantics`] of nondeterministic automata, the type is generic so that each acceptance
/// condition gets them, see the [module](self) documentation.
///
/// Finite words are checked by tracking the set of states that the runs can be in. For an infinite
/// word `u v^ω`, the runs are tracked through `u` and then the product of the automaton with the
/// cycle `v` is searched for a good cycle, see [`CycleCondition`]. This takes time linear in
/// `|v|` times the size of the automaton for most conditions.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Existential<C>(pub C);

/// Decides [`Existential`] semantics for a kind of word ([`Finite`] or [`Omega`]). This is what
/// lets [`Existential`] have one [`Semantics`] implementation for both.
pub trait ExistentialKind<T: TransitionSystem, W, C> {
    /// Returns true if some run of `ts` on `word` from `initial` satisfies `condition`.
    fn some_run_accepts(condition: &C, ts: &T, initial: StateIndex<T>, word: W) -> bool;
}

impl<T, W, C> ExistentialKind<T, W, C> for Finite
where
    T: TransitionSystem,
    W: FiniteWord<Symbol = SymbolOf<T>>,
    C: FinalStateCondition<StateColor = StateColor<T>>,
{
    fn some_run_accepts(condition: &C, ts: &T, initial: StateIndex<T>, word: W) -> bool {
        reached(ts, vec![initial], word.symbols())
            .into_iter()
            .any(|q| {
                ts.state_color(q)
                    .is_some_and(|c| condition.accepts_final(&c))
            })
    }
}

impl<T, W, C> ExistentialKind<T, W, C> for Omega
where
    T: TransitionSystem,
    W: OmegaWord<Symbol = SymbolOf<T>>,
    C: CycleCondition<Color = EdgeColor<T>>,
    EdgeColor<T>: Hash + Eq,
{
    fn some_run_accepts(condition: &C, ts: &T, initial: StateIndex<T>, word: W) -> bool {
        let after_spoke = reached(ts, vec![initial], word.spoke().symbols());
        let cycle = word.cycle_vec();
        let view = CycleProduct { ts, cycle: &cycle };
        let roots = after_spoke
            .into_iter()
            .map(|q| ProductIndex(q, 0))
            .collect();
        search(&view, roots, condition, |_, _| Some(())).is_some()
    }
}

impl<T, W, C> Semantics<T, W> for Existential<C>
where
    T: TransitionSystem,
    W: Word,
    W::Kind: ExistentialKind<T, W, C>,
{
    type Output = bool;
    fn output(&self, ts: &T, initial: StateIndex<T>, word: W) -> Option<bool> {
        Some(<W::Kind as ExistentialKind<T, W, C>>::some_run_accepts(
            &self.0, ts, initial, word,
        ))
    }
}

/// The states that the runs from `current` can be in after reading `symbols`.
fn reached<T: TransitionSystem>(
    ts: &T,
    mut current: Vec<StateIndex<T>>,
    symbols: impl IntoIterator<Item = SymbolOf<T>>,
) -> Vec<StateIndex<T>> {
    for sym in symbols {
        let mut next: Vec<_> = current
            .iter()
            .filter_map(|&q| ts.edges_from(q))
            .flatten()
            .filter(|edge| sym.matches(edge.expression()))
            .map(|edge| edge.target())
            .collect();
        next.sort_unstable();
        next.dedup();
        current = next;
        if current.is_empty() {
            break;
        }
    }
    current
}

/// An edge of a transition system, given by its source, a symbol that takes it and its target.
pub(crate) type Through<T> = (StateIndex<T>, SymbolOf<T>, StateIndex<T>);

/// Decomposes the part of `ts` that is reachable from `roots` into strongly connected components
/// and calls `visit` for each component whose edge colors satisfy `condition`, until it returns
/// `Some`. Components that do not satisfy it are decomposed again without the colors that
/// [`CycleCondition::avoid`] names. `visit` also gets one edge for each color of the component, a
/// cycle through these edges sees exactly the colors of the component.
pub(crate) fn search<T, C, R>(
    ts: &T,
    roots: Vec<StateIndex<T>>,
    condition: &C,
    mut visit: impl for<'v> FnMut(&Scc<'v, Avoiding<'v, T>>, &[Through<T>]) -> Option<R>,
) -> Option<R>
where
    T: TransitionSystem,
    C: CycleCondition<Color = EdgeColor<T>>,
    EdgeColor<T>: Hash + Eq,
{
    struct Task<I, C> {
        roots: Vec<I>,
        avoid: math::FxIndexSet<C>,
        restrict: bool,
    }
    // The same component can be reached by avoiding the same colors in a different order, so the
    // tasks are deduplicated by their sorted states and the indices of the colors they avoid.
    let mut palette = math::FxIndexSet::default();
    let mut seen = math::FxIndexSet::default();
    let mut tasks = vec![Task {
        roots,
        avoid: math::FxIndexSet::default(),
        restrict: false,
    }];
    while let Some(task) = tasks.pop() {
        // built only for tasks that are actually looked at
        let inside: Option<math::FxIndexSet<_>> =
            task.restrict.then(|| task.roots.iter().copied().collect());
        let view = Avoiding {
            ts,
            avoid: &task.avoid,
            inside: inside.as_ref(),
        };
        let sccs = Sccs::on(&view).from(task.roots).compute();
        for scc in sccs.sccs_iter().filter(|scc| scc.is_nontransient()) {
            let mut colors = math::FxIndexSet::default();
            let mut through = Vec::new();
            for edge in scc.interior_edges() {
                let Some(symbol) = edge.expression().symbols().next() else {
                    continue;
                };
                if colors.insert(edge.color().clone()) {
                    through.push((edge.source(), symbol, edge.target()));
                }
            }
            if colors.is_empty() {
                continue;
            }
            if condition.satisfied_by(&colors) {
                if let Some(found) = visit(scc, &through) {
                    return Some(found);
                }
                continue;
            }
            let mut states: Vec<_> = scc.state_indices().copied().collect();
            states.sort_unstable();
            for more in condition.avoid(&colors) {
                let mut avoid = task.avoid.clone();
                avoid.extend(more);
                // a task has to avoid a color of the component, otherwise it would be the same
                if !colors.iter().any(|color| avoid.contains(color)) {
                    continue;
                }
                let mut key: Vec<usize> = avoid
                    .iter()
                    .map(|color| palette.insert_full(color.clone()).0)
                    .collect();
                key.sort_unstable();
                if seen.insert((states.clone(), key)) {
                    tasks.push(Task {
                        roots: states.clone(),
                        avoid,
                        restrict: true,
                    });
                }
            }
        }
    }
    None
}

/// The part of a transition system without the edges of some colors and, optionally, restricted
/// to a set of states. See [`search`].
pub(crate) struct Avoiding<'a, T: TransitionSystem> {
    ts: &'a T,
    avoid: &'a math::FxIndexSet<EdgeColor<T>>,
    inside: Option<&'a math::FxIndexSet<StateIndex<T>>>,
}

/// The edges of an [`Avoiding`] view that start in a state.
pub(crate) struct AvoidingEdges<'a, T: TransitionSystem> {
    it: T::EdgesFromIter<'a>,
    view: &'a Avoiding<'a, T>,
}

impl<'a, T: TransitionSystem> Iterator for AvoidingEdges<'a, T>
where
    EdgeColor<T>: Hash + Eq,
{
    type Item = EdgeOf<'a, T>;
    fn next(&mut self) -> Option<Self::Item> {
        let Avoiding { avoid, inside, .. } = self.view;
        self.it.find(|edge| {
            (avoid.is_empty() || !avoid.contains(edge.color()))
                && inside.is_none_or(|set| set.contains(&edge.target()))
        })
    }
}

impl<'a, T: TransitionSystem> TransitionSystem for Avoiding<'a, T>
where
    EdgeColor<T>: Hash + Eq,
{
    type Alphabet = T::Alphabet;
    type StateIndex = T::StateIndex;
    type StateColor = T::StateColor;
    type EdgeColor = T::EdgeColor;
    type EdgesFromIter<'this>
        = AvoidingEdges<'this, T>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.ts.state_color(state)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(AvoidingEdges {
            it: self.ts.edges_from(state)?,
            view: self,
        })
    }

    fn state_bound(&self) -> Option<usize> {
        self.ts.state_bound()
    }
}

/// The product of a transition system with the cycle of an ultimately periodic word: a state
/// `(q, i)` stands for `q` before reading the `i`-th symbol of `cycle`, and its edges are those of
/// `q` that match that symbol.
struct CycleProduct<'a, T: TransitionSystem> {
    ts: &'a T,
    cycle: &'a [SymbolOf<T>],
}

/// The edges of a [`CycleProduct`] that start in a state.
struct CycleProductEdges<'a, T: TransitionSystem + 'a> {
    it: T::EdgesFromIter<'a>,
    position: usize,
    symbol: SymbolOf<T>,
    next: usize,
}

impl<'a, T: TransitionSystem + 'a> Iterator for CycleProductEdges<'a, T> {
    type Item = EdgeRef<'a, ProductIndex<T::StateIndex, usize>, EdgeExpression<T>, T::EdgeColor>;
    fn next(&mut self) -> Option<Self::Item> {
        let edge = self
            .it
            .find(|edge| self.symbol.matches(edge.expression()))?;
        Some(EdgeRef::owned(
            ProductIndex(edge.source(), self.position),
            edge.expression(),
            edge.color().clone(),
            ProductIndex(edge.target(), self.next),
        ))
    }
}

impl<'a, T: TransitionSystem> TransitionSystem for CycleProduct<'a, T> {
    type Alphabet = T::Alphabet;
    type StateIndex = ProductIndex<T::StateIndex, usize>;
    type StateColor = T::StateColor;
    type EdgeColor = T::EdgeColor;
    type EdgesFromIter<'this>
        = CycleProductEdges<'this, T>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        self.ts.state_color(state.0)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        let ProductIndex(q, position) = state;
        Some(CycleProductEdges {
            it: self.ts.edges_from(q)?,
            position,
            symbol: *self.cycle.get(position)?,
            next: (position + 1) % self.cycle.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::automaton::{
        BuchiCondition, CoBuchiCondition, Existential, MinEvenParityCondition, MullerCondition,
        RabinCondition, RabinPair,
    };
    use crate::prelude::*;
    use crate::word::ReducedOmegaWord;

    /// All ultimately periodic words `u v^ω` over `{a, b}` with `|u| <= 2` and `1 <= |v| <= 3`.
    fn words() -> Vec<ReducedOmegaWord<char>> {
        let upto = |n: usize, min: usize| {
            let mut all = vec![String::new()];
            for _ in 0..n {
                let longer: Vec<_> = all
                    .iter()
                    .flat_map(|w| ["a", "b"].map(|c| format!("{w}{c}")))
                    .collect();
                all.extend(longer);
            }
            all.sort();
            all.dedup();
            all.retain(|w| w.len() >= min);
            all
        };
        let mut words = Vec::new();
        for u in upto(2, 0) {
            for v in upto(3, 1) {
                words.push(upw!(u.as_str(), v.as_str()));
            }
        }
        words
    }

    /// Edges of a pseudo-random automaton with `n` states, two edges per state and symbol and
    /// priorities below 4, so that the automaton is nondeterministic.
    fn random_edges(seed: u64, n: u32) -> Vec<(u32, char, Int, u32)> {
        let mut state = seed;
        let mut next = |bound: u32| {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            ((state >> 33) % bound as u64) as u32
        };
        let mut edges = Vec::new();
        for q in 0..n {
            for sym in ['a', 'b'] {
                for _ in 0..2 {
                    edges.push((q, sym, next(4) as Int, next(n)));
                }
            }
        }
        edges.sort();
        edges.dedup_by_key(|e| (e.0, e.1, e.3));
        edges
    }

    #[test]
    fn parity_rabin_and_muller_agree_on_nondeterministic_automata() {
        // min even parity over 0..4 as a Rabin condition and as a Muller condition
        let rabin: RabinCondition<Int> = [
            RabinPair::from_iters([], [0]),
            RabinPair::from_iters([0, 1], [2]),
        ]
        .into();
        let subsets: Vec<Vec<Int>> = (1u8..16)
            .map(|bits| (0..4).filter(|p| bits & (1 << p) != 0).collect())
            .filter(|set: &Vec<Int>| set[0].is_multiple_of(2))
            .collect();
        let muller = MullerCondition::from_iter_iter(subsets);
        for seed in 0..20 {
            let edges = random_edges(seed, 4);
            let npa = Builder::without_state_colors()
                .with_transitions(edges.clone())
                .into_npa(0);
            let nra = Builder::without_state_colors()
                .with_transitions(edges.clone())
                .into_nondeterministic_automaton(0, Existential(rabin.clone()));
            let nma = Builder::without_state_colors()
                .with_transitions(edges)
                .into_nondeterministic_automaton(0, Existential(muller.clone()));
            let mut accepts_some = false;
            for word in words() {
                let expected = npa.accepts(&word);
                accepts_some |= expected;
                assert_eq!(nra.accepts(&word), expected, "seed {seed}, {word:?}");
                assert_eq!(nma.accepts(&word), expected, "seed {seed}, {word:?}");
            }
            // a witness is accepted, and an empty language accepts none of the words
            let witnesses = [
                Emptiness::of(&npa).witness(),
                Emptiness::of(&nra).witness(),
                Emptiness::of(&nma).witness(),
            ];
            for witness in &witnesses {
                assert_eq!(witness.is_some(), witnesses[0].is_some(), "seed {seed}");
                if let Some(word) = witness {
                    assert!(npa.accepts(word), "seed {seed}, {word:?}");
                }
            }
            assert!(witnesses[0].is_some() || !accepts_some, "seed {seed}");
        }
    }

    #[test]
    fn nfa_problems() {
        // second to last symbol is an `a`, and words that contain an `a`
        let second_to_last = Builder::without_edge_colors()
            .with_state_colors([false, false, true])
            .with_transitions([
                (0, 'a', 0),
                (0, 'b', 0),
                (0, 'a', 1),
                (1, 'a', 2),
                (1, 'b', 2),
            ])
            .into_nfa(0);
        let contains_a = Builder::without_edge_colors()
            .with_state_colors([false, true])
            .with_transitions([
                (0, 'a', 0),
                (0, 'b', 0),
                (0, 'a', 1),
                (1, 'a', 1),
                (1, 'b', 1),
            ])
            .into_nfa(0);
        assert_eq!(
            Emptiness::of(&second_to_last).witness(),
            Some(vec!['a', 'a'])
        );
        assert!(Inclusion::of(&second_to_last).within(&contains_a).holds());
        assert_eq!(
            Inclusion::of(&contains_a)
                .within(&second_to_last)
                .counterexample(),
            Some(vec!['a'])
        );
        assert!(!Equivalence::of(&contains_a).and(&second_to_last).holds());
    }

    #[test]
    fn existential_agrees_with_deterministic_semantics() {
        for seed in 0..20 {
            // keep the first edge per state and symbol, which makes the automaton deterministic
            let mut edges = random_edges(seed, 4);
            edges.dedup_by_key(|e| (e.0, e.1));
            let dpa = Builder::without_state_colors()
                .with_transitions(edges.clone())
                .into_dpa(0);
            let bools: Vec<_> = edges
                .iter()
                .map(|&(p, a, c, q)| (p, a, c == 0, q))
                .collect();
            let dba = Builder::without_state_colors()
                .with_transitions(bools.clone())
                .into_dba(0);
            let dcw = Builder::without_state_colors()
                .with_transitions(bools)
                .into_dcw(0);
            for word in words() {
                let some_run = |sem_accepts: bool, existential: bool| {
                    assert_eq!(sem_accepts, existential, "seed {seed}, {word:?}");
                };
                let (ts, q) = (dpa.ts(), dpa.initial());
                some_run(
                    dpa.accepts(&word),
                    Existential(MinEvenParityCondition)
                        .output(ts, q, &word)
                        .unwrap(),
                );
                let (ts, q) = (dba.ts(), dba.initial());
                some_run(
                    dba.accepts(&word),
                    Existential(BuchiCondition).output(ts, q, &word).unwrap(),
                );
                let (ts, q) = (dcw.ts(), dcw.initial());
                some_run(
                    dcw.accepts(&word),
                    Existential(CoBuchiCondition).output(ts, q, &word).unwrap(),
                );
            }
        }
    }

    #[test]
    fn runs_that_die_do_not_accept() {
        // only `a` can be read forever, `b` leads nowhere
        let nba = Builder::without_state_colors()
            .with_transitions([(0, 'a', true, 0), (0, 'a', false, 1)])
            .into_nba(0);
        assert!(nba.accepts(upw!("a")));
        assert!(!nba.accepts(upw!("ab")));
        assert!(!nba.accepts(upw!("b", "a")));
        let nfa = Builder::without_edge_colors()
            .with_state_colors([false, true])
            .with_transitions([(0, 'a', 0), (0, 'a', 1)])
            .into_nfa(0);
        assert!(nfa.accepts("aa"));
        assert!(!nfa.accepts("ab"));
        assert!(!nfa.accepts(""));
    }
}
