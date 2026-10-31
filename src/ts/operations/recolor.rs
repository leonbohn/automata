use crate::representation::{IntoTransitions, OwnedEdge, Parts};
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{Deterministic, EdgeExpression, EdgeOf, EdgeRef, StateIndex, SymbolOf};
use crate::{Color, Pointed, States, TransitionSystem, Void, math};
use std::borrow::Cow;
use std::hash::Hash;
use std::marker::PhantomData;

/// Computes the colors of the states of a [`Recolor`] from the colors of the states of the
/// wrapped system `T`. It is implemented by [`Keep`], by closures `Fn(StateIndex, &Q) -> Q2` and by
/// the wrappers [`StateColorFn`] and [`Provided`].
pub trait StateRecolor<T: TransitionSystem> {
    /// The new type of state colors.
    type Color: Color;
    /// Returns the new color of `state`, which had the color `color`.
    fn recolor<'a>(
        &self,
        state: StateIndex<T>,
        color: Cow<'a, T::StateColor>,
    ) -> Cow<'a, Self::Color>;
}

/// Computes the colors of the edges of a [`Recolor`] from the edges of the wrapped system `T`. It
/// is implemented by [`Keep`], by closures `Fn(&EdgeRef) -> C2` and by the wrappers [`ColorFn`] and
/// [`EdgeFn`]. It is used for successors and predecessors alike.
pub trait EdgeRecolor<T: TransitionSystem> {
    /// The new type of edge colors.
    type Color: Color;
    /// Returns `edge` with its new color.
    fn recolor<'a>(
        &self,
        edge: EdgeOf<'a, T>,
    ) -> EdgeRef<'a, StateIndex<T>, EdgeExpression<T>, Self::Color>;
}

/// Leaves the state colors or the edge colors of a [`Recolor`] as they are.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Keep;

impl<T: TransitionSystem> StateRecolor<T> for Keep {
    type Color = T::StateColor;
    #[inline(always)]
    fn recolor<'a>(
        &self,
        _state: StateIndex<T>,
        color: Cow<'a, T::StateColor>,
    ) -> Cow<'a, Self::Color> {
        color
    }
}

impl<T: TransitionSystem> EdgeRecolor<T> for Keep {
    type Color = T::EdgeColor;
    #[inline(always)]
    fn recolor<'a>(&self, edge: EdgeOf<'a, T>) -> EdgeOf<'a, T> {
        edge
    }
}

impl<T, Q, F> StateRecolor<T> for F
where
    T: TransitionSystem,
    Q: Color,
    F: Fn(StateIndex<T>, &T::StateColor) -> Q,
{
    type Color = Q;
    #[inline(always)]
    fn recolor<'a>(&self, state: StateIndex<T>, color: Cow<'a, T::StateColor>) -> Cow<'a, Q> {
        Cow::Owned(self(state, &color))
    }
}

impl<T, C, F> EdgeRecolor<T> for F
where
    T: TransitionSystem,
    C: Color,
    F: Fn(&EdgeOf<'_, T>) -> C,
{
    type Color = C;
    #[inline(always)]
    fn recolor<'a>(&self, edge: EdgeOf<'a, T>) -> EdgeRef<'a, StateIndex<T>, EdgeExpression<T>, C> {
        let color = self(&edge);
        edge.with_color(Cow::Owned(color))
    }
}

/// Maps the state colors with a function that only looks at the color, see
/// [`TransitionSystem::map_state_colors`].
#[derive(Clone, Copy, Debug)]
pub struct StateColorFn<F>(pub F);

impl<T: TransitionSystem, Q: Color, F: Fn(T::StateColor) -> Q> StateRecolor<T> for StateColorFn<F> {
    type Color = Q;
    #[inline(always)]
    fn recolor<'a>(&self, _state: StateIndex<T>, color: Cow<'a, T::StateColor>) -> Cow<'a, Q> {
        Cow::Owned((self.0)(color.into_owned()))
    }
}

/// Maps the edge colors with a function that only looks at the color, see
/// [`TransitionSystem::map_edge_colors`].
#[derive(Clone, Copy, Debug)]
pub struct ColorFn<F>(pub F);

impl<T: TransitionSystem, C: Color, F: Fn(T::EdgeColor) -> C> EdgeRecolor<T> for ColorFn<F> {
    type Color = C;
    #[inline(always)]
    fn recolor<'a>(&self, edge: EdgeOf<'a, T>) -> EdgeRef<'a, StateIndex<T>, EdgeExpression<T>, C> {
        let (source, target) = (edge.source(), edge.target());
        let expression = edge.expression();
        EdgeRef::owned(
            source,
            expression,
            (self.0)(edge.into_color().into_owned()),
            target,
        )
    }
}

/// Maps the edge colors with a function that is also given source, expression and target of
/// the edge, see [`TransitionSystem::map_edge_colors_full`].
#[derive(Clone, Copy, Debug)]
pub struct EdgeFn<F>(pub F);

impl<T, C, F> EdgeRecolor<T> for EdgeFn<F>
where
    T: TransitionSystem,
    C: Color,
    F: Fn(StateIndex<T>, &EdgeExpression<T>, T::EdgeColor, StateIndex<T>) -> C,
{
    type Color = C;
    #[inline(always)]
    fn recolor<'a>(&self, edge: EdgeOf<'a, T>) -> EdgeRef<'a, StateIndex<T>, EdgeExpression<T>, C> {
        let (source, target) = (edge.source(), edge.target());
        let expression = edge.expression();
        let color = (self.0)(source, expression, edge.into_color().into_owned(), target);
        EdgeRef::owned(source, expression, color, target)
    }
}

/// Implementors of this trait provide a color for states of a
/// [`TransitionSystem`] that are indexed by the type `Idx` and
/// the output color is given by the associated type `Color`.
///
/// Naturally, a color itself provides a state color, namely by
/// associating each state with itself. A [`math::FxIndexMap`] does not
/// implement the trait, as it may have no entry for a state. Wrap it in a
/// [`DefaultIfMissing`] to provide a default color for missing entries.
pub trait ProvidesStateColor<Idx> {
    /// The output color given to each state.
    type Color: Color;
    /// Returns the color assigned to the given `state`. The coloring is
    /// assumed to be complete, i.e. there is a color for every possible `Idx`.
    fn state_color(&self, state: Idx) -> Self::Color;
}

/// Provides a uniform color for all states of a [`TransitionSystem`]. The main use case for
/// this struct is when calling [`TransitionSystem::with_state_color`] and providing a single
/// color for all states.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct UniformColor<C: Color>(pub C);

impl<Idx, C: Color> ProvidesStateColor<Idx> for UniformColor<C> {
    type Color = C;
    fn state_color(&self, _state: Idx) -> Self::Color {
        self.0.clone()
    }
}

impl<Idx, C: Color, F: Fn(Idx) -> C> ProvidesStateColor<Idx> for F {
    type Color = C;
    fn state_color(&self, state: Idx) -> Self::Color {
        (self)(state)
    }
}

/// Augments a [`math::FxIndexMap`] with a default color for missing
/// entries. This struct implements [`ProvidesStateColor`] and
/// wrapping an incomplete map is its only purpose.
///
/// Specifically, it returns the color stored in the [`math::FxIndexMap`]
/// it wraps for a `state` if present and the stored `default`
/// value otherwise.
#[derive(Clone, Eq, PartialEq)]
pub struct DefaultIfMissing<X: Hash + Eq, Y> {
    map: math::FxIndexMap<X, Y>,
    default: Y,
}

impl<X: Hash + Eq, Y: Color> DefaultIfMissing<X, Y> {
    /// Creates a new instance of `Self` from a given (partial)
    /// map and default value.
    pub fn new(map: math::FxIndexMap<X, Y>, default: Y) -> Self {
        Self { map, default }
    }
}

impl<Idx: Hash + Eq, Y: Color> ProvidesStateColor<Idx> for DefaultIfMissing<Idx, Y> {
    type Color = Y;

    fn state_color(&self, state: Idx) -> Self::Color {
        self.map
            .get(&state)
            .cloned()
            .unwrap_or(self.default.clone())
    }
}

/// Gives the states the colors of a [`ProvidesStateColor`], see [`TransitionSystem::with_state_color`].
#[derive(Clone, Debug)]
pub struct Provided<P>(pub P);

impl<T: TransitionSystem, P: ProvidesStateColor<StateIndex<T>>> StateRecolor<T> for Provided<P> {
    type Color = P::Color;
    #[inline(always)]
    fn recolor<'a>(
        &self,
        state: StateIndex<T>,
        _color: Cow<'a, T::StateColor>,
    ) -> Cow<'a, P::Color> {
        Cow::Owned(self.0.state_color(state))
    }
}

/// A transition system whose state colors and edge colors are computed from those of the wrapped
/// system `T`. All the `map_*`, `erase_*` and `with_state_color` methods of
/// [`TransitionSystem`] build one.
///
/// Like the adapters of [`Iterator`], a `Recolor` is **lazy**: the closures run whenever a color
/// is accessed and nothing is cached or stored. Colors that are used a lot should be
/// materialized with `collect`.
#[derive(Clone, Debug)]
pub struct Recolor<T, FS = Keep, FE = Keep> {
    ts: T,
    state: FS,
    edge: FE,
}

/// The transition system that results from erasing all colors, c.f.
/// [`TransitionSystem::erase_colors`].
pub type EraseColors<T> = Recolor<
    T,
    StateColorFn<fn(<T as TransitionSystem>::StateColor) -> Void>,
    ColorFn<fn(<T as TransitionSystem>::EdgeColor) -> Void>,
>;

/// The transition system that results from erasing the state colors, c.f.
/// [`TransitionSystem::erase_state_colors`].
pub type EraseStateColors<T> =
    Recolor<T, StateColorFn<fn(<T as TransitionSystem>::StateColor) -> Void>, Keep>;

/// The transition system that results from erasing the edge colors, c.f.
/// [`TransitionSystem::erase_edge_colors`].
pub type EraseEdgeColors<T> =
    Recolor<T, Keep, ColorFn<fn(<T as TransitionSystem>::EdgeColor) -> Void>>;

impl<T, FS, FE> Recolor<T, FS, FE> {
    /// Wraps `ts`, recoloring its states with `state` and its edges with `edge`.
    pub fn new(ts: T, state: FS, edge: FE) -> Self {
        Self { ts, state, edge }
    }

    /// Returns a reference to the underlying transition system.
    pub fn ts(&self) -> &T {
        &self.ts
    }

    /// Decomposes `self` into the transition system and the recoloring of states and edges.
    pub fn into_parts(self) -> (T, FS, FE) {
        (self.ts, self.state, self.edge)
    }
}

/// Iterator over edges whose colors are recolored, used for successors and predecessors.
#[derive(Clone, Debug)]
pub struct RecolorEdges<'a, I, R, T> {
    it: I,
    recolor: &'a R,
    _ts: PhantomData<fn() -> T>,
}

impl<'a, T, I, R> Iterator for RecolorEdges<'a, I, R, T>
where
    T: TransitionSystem + 'a,
    R::Color: 'a,
    I: Iterator<Item = EdgeOf<'a, T>>,
    R: EdgeRecolor<T>,
{
    type Item = EdgeRef<'a, StateIndex<T>, EdgeExpression<T>, R::Color>;
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.it.next().map(|e| self.recolor.recolor(e))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

impl<T, FS, FE> TransitionSystem for Recolor<T, FS, FE>
where
    T: TransitionSystem,
    FS: StateRecolor<T>,
    FE: EdgeRecolor<T>,
{
    type Alphabet = T::Alphabet;
    type StateIndex = T::StateIndex;
    type StateColor = FS::Color;
    type EdgeColor = FE::Color;

    type EdgesFromIter<'this>
        = RecolorEdges<'this, T::EdgesFromIter<'this>, FE, T>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(RecolorEdges {
            it: self.ts.edges_from(state)?,
            recolor: &self.edge,
            _ts: PhantomData,
        })
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Cow<'_, Self::StateColor>> {
        Some(self.state.recolor(state, self.ts.state_color(state)?))
    }

    fn state_bound(&self) -> Option<usize> {
        self.ts.state_bound()
    }
}

impl<T, FS, FE> States for Recolor<T, FS, FE>
where
    T: States,
    FS: StateRecolor<T>,
    FE: EdgeRecolor<T>,
{
    type StatesIter<'this>
        = T::StatesIter<'this>
    where
        Self: 'this;

    fn states(&self) -> Self::StatesIter<'_> {
        self.ts.states()
    }

    fn contains_state(&self, index: StateIndex<Self>) -> bool {
        self.ts.contains_state(index)
    }

    fn state_count(&self) -> usize {
        self.ts.state_count()
    }
}

/// Iterator over the recolored states of a [`Recolor`] that is consumed.
pub struct RecolorIntoStates<I, R, T> {
    it: I,
    recolor: R,
    _ts: PhantomData<fn() -> T>,
}

impl<T, I, R> Iterator for RecolorIntoStates<I, R, T>
where
    T: TransitionSystem,
    I: Iterator<Item = (StateIndex<T>, T::StateColor)>,
    R: StateRecolor<T>,
{
    type Item = (StateIndex<T>, R::Color);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let (q, color) = self.it.next()?;
        Some((q, self.recolor.recolor(q, Cow::Owned(color)).into_owned()))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

/// Iterator over the recolored edges of a [`Recolor`] that is consumed.
pub struct RecolorIntoEdges<I, R, T> {
    it: I,
    recolor: R,
    _ts: PhantomData<fn() -> T>,
}

impl<T, I, R> Iterator for RecolorIntoEdges<I, R, T>
where
    T: TransitionSystem,
    I: Iterator<Item = OwnedEdge<T>>,
    R: EdgeRecolor<T>,
{
    type Item = (StateIndex<T>, EdgeExpression<T>, R::Color, StateIndex<T>);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let (source, expression, color, target) = self.it.next()?;
        let (source, target, color) = {
            let recolored =
                self.recolor
                    .recolor(EdgeRef::owned(source, &expression, color, target));
            (
                recolored.source(),
                recolored.target(),
                recolored.into_color().into_owned(),
            )
        };
        Some((source, expression, color, target))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

impl<T, FS, FE> IntoTransitions for Recolor<T, FS, FE>
where
    T: IntoTransitions,
    FS: StateRecolor<T>,
    FE: EdgeRecolor<T>,
{
    type Initial = T::Initial;
    type IntoStates = RecolorIntoStates<T::IntoStates, FS, T>;
    type IntoEdges = RecolorIntoEdges<T::IntoEdges, FE, T>;

    fn into_transitions(
        self,
    ) -> Parts<Self::Alphabet, Self::IntoStates, Self::IntoEdges, Self::Initial> {
        let Parts {
            alphabet,
            states,
            edges,
            initial,
        } = self.ts.into_transitions();
        Parts {
            alphabet,
            states: RecolorIntoStates {
                it: states,
                recolor: self.state,
                _ts: PhantomData,
            },
            edges: RecolorIntoEdges {
                it: edges,
                recolor: self.edge,
                _ts: PhantomData,
            },
            initial,
        }
    }
}

impl<T, FS, FE> Pointed for Recolor<T, FS, FE>
where
    T: Pointed,
    FS: StateRecolor<T>,
    FE: EdgeRecolor<T>,
{
    fn initial(&self) -> Self::StateIndex {
        self.ts.initial()
    }
}

impl<T, FS, FE> Deterministic for Recolor<T, FS, FE>
where
    T: Deterministic,
    FS: StateRecolor<T>,
    FE: EdgeRecolor<T>,
{
    fn edge(&self, state: StateIndex<Self>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        Some(self.edge.recolor(self.ts.edge(state, symbol)?))
    }
}

impl<T, FS, FE> PredecessorIterable for Recolor<T, FS, FE>
where
    T: PredecessorIterable,
    FS: StateRecolor<T>,
    FE: EdgeRecolor<T>,
{
    type EdgesToIter<'this>
        = RecolorEdges<'this, T::EdgesToIter<'this>, FE, T>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Some(RecolorEdges {
            it: self.ts.predecessors(state)?,
            recolor: &self.edge,
            _ts: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::ts::operations::UniformColor;
    use crate::ts::{Builder, Deterministic, PredecessorIterable, States};
    use crate::{TransitionSystem, Void};
    use std::cell::Cell;

    fn ts() -> crate::DTS<crate::alphabet::CharAlphabet, bool, u8> {
        Builder::default()
            .with_state_colors([true, false, false])
            .with_edges([
                (0, 'a', 1u8, 1),
                (1, 'a', 2, 2),
                (2, 'a', 3, 0),
                (0, 'b', 4, 0),
            ])
            .into_dts()
    }

    #[test]
    fn edge_colors_are_mapped_for_successors_predecessors_and_lookups() {
        let mapped = ts().map_edge_colors(|c| u32::from(c) * 10);
        let mut out: Vec<_> = mapped
            .edges_from(0)
            .unwrap()
            .map(|e| (e.target(), *e.color()))
            .collect();
        out.sort();
        assert_eq!(out, vec![(0, 40), (1, 10)]);
        let mut preds: Vec<_> = mapped
            .predecessors(0)
            .unwrap()
            .map(|e| (e.source(), e.target(), *e.color()))
            .collect();
        preds.sort();
        assert_eq!(preds, vec![(0, 0, 40), (2, 0, 30)]);
        assert_eq!(*mapped.edge(1, 'a').unwrap().color(), 20);
    }

    #[test]
    fn full_edge_recoloring_sees_source_expression_and_target() {
        let mapped = ts().map_edge_colors_full(|p, a: &char, c, q| format!("{p}{a}{c}{q}"));
        assert_eq!(mapped.edge(1, 'a').unwrap().color(), "1a22");
        let pred = mapped.predecessors(2).unwrap().next().unwrap();
        assert_eq!(pred.color(), "1a22");
    }

    #[test]
    fn state_colors_are_mapped_or_provided() {
        let mapped = ts().map_state_colors(|c| if c { 1u8 } else { 0 });
        assert_eq!(mapped.state_color(0).as_deref(), Some(&1));
        assert_eq!(mapped.state_color(1).as_deref(), Some(&0));
        let uniform = ts().with_state_color(UniformColor('x'));
        assert!(
            uniform
                .states()
                .all(|q| uniform.state_color(q).as_deref() == Some(&'x'))
        );
        let by_index = ts().with_state_color(|q: u32| q * 2);
        assert_eq!(by_index.state_color(2).as_deref(), Some(&4));
    }

    #[test]
    fn erased_colors_are_void() {
        let erased = ts().erase_colors();
        assert_eq!(erased.state_color(0).as_deref(), Some(&Void));
        assert_eq!(erased.edge(0, 'a').unwrap().color(), &Void);
    }

    #[test]
    fn recoloring_is_lazy_and_nothing_is_cached() {
        let calls = Cell::new(0);
        let mapped = ts().map_edge_colors(|c| {
            calls.set(calls.get() + 1);
            c
        });
        assert_eq!(
            calls.get(),
            0,
            "building the adapter must not run the closure"
        );
        let _ = mapped.edge(0, 'a');
        let _ = mapped.edge(0, 'a');
        assert_eq!(calls.get(), 2, "every access runs the closure");
    }
}
