use crate::alphabet::{Alphabet, IndexedAlphabet};
use crate::ts::States;
use crate::{Pointed, TransitionSystem};
use fixedbitset::FixedBitSet;
use itertools::Itertools;

use super::{EdgeColor, EdgeId, IntoEdgeTuple, SproutableStorage, StateColor, StateIndex};

/// Implemented by [`TransitionSystem`]s (TS) that can be created for a given [`Alphabet`],
/// which is may be used in conjunction with [`Sproutable`] to successively grow a
/// TS.
///
/// Usually, this will *not* be implemented by TS that have a [designated initial state](`Pointed`).
/// For those, a dedicated method should be used.
pub trait ForAlphabet<A: Alphabet>: Sized {
    /// Creates an instance of `Self` for the given [`Alphabet`]. The resulting
    /// TS should be empty.
    fn for_alphabet(from: A) -> Self;

    /// Creates an instance of `Self` for the given [`Alphabet`] and a hint for the size of the transition
    /// system allowing for preallocation of memory. The resulting TS should be empty.
    fn for_alphabet_size_hint(from: A, _size_hint: usize) -> Self {
        Self::for_alphabet(from)
    }
}

/// Trait for transition systems that allow insertion of states and transitions.
pub trait Sproutable: States {
    /// The family of storages that `Self` belongs to, so that generic code can name a system of the
    /// same representation with other colors, see [`Storage::Ts`](super::Storage::Ts).
    type Storage: SproutableStorage<Self::Alphabet>;

    /// Adds a new state with the given color. The method returns the index of the newly created
    /// state.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     alphabet::CharAlphabet, Void,
    ///     ts::{Deterministic, ForAlphabet, Builder, Shrinkable, Sproutable, States, TransitionSystem},
    ///     DTS,
    /// };
    ///     
    /// let mut ts = DTS::<_, _, Void>::for_alphabet(CharAlphabet::of_size(3));
    /// let q0 = ts.add_state(false);
    /// let before = ts.state_count();
    /// let q1 = ts.add_state(true);
    /// assert_eq!(ts.state_count(), before + 1);
    /// ```
    /// We need to explicitly give the state color for the created transition system as we do not
    /// add any edges and the type can therefore not be inferred.
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex;

    /// Adds a new edge to the transition system and returns its [`EdgeId`], which stays valid until
    /// the edge is removed. If the system is deterministic, edges that overlap with the new one are
    /// replaced.
    ///
    /// The details of the edge are given as a type that implements [`IntoEdgeTuple`]. This allows
    /// for a more flexible way of adding edges, as the method can be called with a tuple, a struct
    /// or any other type that can be converted into a tuple of the form
    /// `(StateIndex, Expression, EdgeColor, StateIndex)`. Moreover, if `EdgeColor` is `Void`, then
    /// we can simply call the method with a tuple of the form `(StateIndex, Expression, StateIndex)`
    /// and the method will automatically convert the tuple into the correct form.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     alphabet::CharAlphabet,
    ///     ts::{Deterministic, ForAlphabet, Builder, Shrinkable, Sproutable, TransitionSystem},
    ///     DTS,
    /// };
    ///
    /// let mut ts = DTS::for_alphabet(CharAlphabet::of_size(3));
    /// let q0 = ts.add_state(false);
    /// let q1 = ts.add_state(true);
    /// assert!(ts.edge(q0, 'a').is_none());
    /// let first = ts.add_edge((q0, 'a', q1));
    /// assert_eq!(ts.successor(q0, 'a'), Some(q1));
    ///
    /// // the system is deterministic, so the new edge replaces the overlapping one
    /// let second = ts.add_edge((q0, 'a', q0));
    /// assert_ne!(first, second);
    /// assert_eq!(ts.successor(q0, 'a'), Some(q0));
    /// assert!(ts.remove_edge(first).is_none());
    /// ```
    fn add_edge<E>(&mut self, t: E) -> EdgeId
    where
        E: IntoEdgeTuple<Self>;

    /// A mutable reference to the color of the edge with the given id, or `None` if there is no such
    /// edge.
    fn edge_color_mut(&mut self, id: EdgeId) -> Option<&mut EdgeColor<Self>>;

    /// A mutable reference to the color of the given state, or `None` if there is no such state.
    fn state_color_mut(&mut self, state: StateIndex<Self>) -> Option<&mut StateColor<Self>>;

    /// Turns the automaton into a complete one, by adding a sink state and adding transitions
    /// to it from all states that do not have a transition for a given symbol.
    ///
    /// The sink state will be colored with `sink_color` and each newly introduced edge will
    /// be colored with `edge_color`.
    ///
    /// # Example
    /// We should be able to take a TS that is not yet complete and use this method to build
    /// one which is complete. For an incomplete transition system, this should result in
    /// a new state being created.
    /// ```
    /// use automata::{
    ///     alphabet::CharAlphabet, Void,
    ///     ts::{Deterministic, ForAlphabet, Builder, Shrinkable, States, TransitionSystem, Sproutable},
    ///     DTS,
    /// };
    ///
    /// let mut ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 0)])
    ///     .with_alphabet_symbols(['a', 'b'])
    ///     .into_dts();
    /// assert!(!ts.is_complete());
    /// ts.complete_with_colors(Void, Void);
    /// assert_eq!(ts.state_count(), 2);
    /// assert!(ts.is_complete());
    /// ```
    ///
    /// However if we call the method on a TS that is already complete, i.e. it has a transition
    /// for every alphabet symbol going out from every state, then the method should return the
    /// original TS unchanged.
    /// ```
    /// use automata::{
    ///     alphabet::CharAlphabet, Void,
    ///     ts::{Deterministic, ForAlphabet, Builder, States, TransitionSystem, Shrinkable, Sproutable},
    ///     DTS,
    /// };
    /// let mut ts = Builder::without_colors()
    ///     .with_edges([(0, 'a', 0), (0, 'b', 0)])
    ///     .with_alphabet_symbols(['a', 'b'])
    ///     .into_dts();
    /// assert!(ts.is_complete());
    /// ts.complete_with_colors(Void, Void);
    /// assert_eq!(ts.state_count(), 1);
    /// assert!(ts.is_complete());
    /// ```
    fn complete_with_colors(&mut self, sink_color: Self::StateColor, edge_color: Self::EdgeColor)
    where
        Self::Alphabet: IndexedAlphabet,
    {
        // in case we are already a complete TS, we can return without changes
        if self.is_complete() {
            return;
        }

        let sink = self.add_state(sink_color);
        for sym in self.alphabet().universe().collect_vec() {
            self.add_edge((
                sink,
                self.alphabet().symbol_to_expression(sym),
                edge_color.clone(),
                sink,
            ));
        }
        let mut seen = FixedBitSet::with_capacity(self.alphabet().size());
        for state in self.states().collect_vec() {
            seen.clear();
            for edge in self.edges_from(state).unwrap() {
                seen.insert(self.alphabet().expression_to_index(edge.expression()));
            }
            for missing in (0..self.alphabet().size()).filter(|i| !seen.contains(*i)) {
                self.add_edge((
                    state,
                    self.alphabet().expression_from_index(missing),
                    edge_color.clone(),
                    sink,
                ));
            }
        }
    }

    /// Add a new states with colors given by an iterator. For each provided color, a new state is
    /// created. Returns an iterator over the indices of the newly created states.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     alphabet::CharAlphabet, Void,
    ///     ts::{Deterministic, TransitionSystem, ForAlphabet, Builder, Shrinkable, Sproutable},
    ///     DTS,
    /// };
    ///
    /// let mut ts = DTS::<_, _, Void>::for_alphabet(CharAlphabet::of_size(3));
    /// let states = ts.extend_states([true, false, true]);
    /// assert_eq!(states.collect::<Vec<_>>(), vec![0, 1, 2]);
    /// ```
    /// We need to explicitly give the edge color for the created transition system as we do not
    /// add any edges and the type can therefore not be inferred.
    fn extend_states<I: IntoIterator<Item = StateColor<Self>>>(
        &mut self,
        iter: I,
    ) -> impl Iterator<Item = Self::StateIndex> {
        iter.into_iter().map(move |color| self.add_state(color))
    }

    /// Sets the color of the state with the given index. If the state does not exist, the method
    /// panics. Usually, we would like to avoid recoloring states individually, and instead
    /// use the [`TransitionSystem::map_state_colors`] method.
    fn set_state_color(&mut self, index: StateIndex<Self>, color: StateColor<Self>) {
        match self.state_color_mut(index) {
            Some(slot) => *slot = color,
            None => panic!("cannot color state {index:?}, it does not exist"),
        }
    }

    /// Sets the state color of the initial state. This method is only available for a ts if it
    /// is [`Pointed`] and it simply obtains the initial state and subsequetly [sets its color](`Self::set_state_color`).
    fn set_initial_color(&mut self, color: StateColor<Self>)
    where
        Self: Pointed,
    {
        self.set_state_color(self.initial(), color);
    }
}

#[cfg(test)]
mod tests {
    use crate::States;
    use crate::alphabet::{Alphabet, CharAlphabet};
    use crate::ts::{Deterministic, ForAlphabet, Sproutable};
    use crate::{DTS, TransitionSystem};

    #[test]
    fn for_alphabet_inference() {
        let mut ts = DTS::for_alphabet(CharAlphabet::of_size(3));
        assert_eq!(ts.alphabet().size(), 3);

        let q0 = ts.add_state(false);
        let q1 = ts.add_state(true);
        assert_eq!(ts.edge(q0, 'a'), None);
        ts.add_edge((q0, 'a', q1));
        assert_eq!(ts.reached_state_from(q0, "a"), Some(q1));
    }

    #[test]
    fn sprout_after_creating() {
        let mut ts = DTS::for_alphabet(CharAlphabet::of_size(3));
        let q0 = ts.add_state(false);
        let q1 = ts.add_state(true);
        assert_eq!(ts.edge(q0, 'a'), None);
        ts.add_edge((q0, 'a', q1));
        assert_eq!(ts.reached_state_from(q0, "a"), Some(q1));
    }

    #[test]
    fn complete_ts() {
        let mut partial = DTS::builder()
            .default_color(())
            .with_transitions([
                (0, 'a', 0, 0),
                (0, 'b', 0, 0),
                (0, 'c', 0, 1),
                (1, 'a', 0, 0),
            ])
            .into_dts();
        assert_eq!(partial.reached_state_from(0, "aaacb"), None);
        assert!(!partial.is_complete());

        partial.complete_with_colors((), 2);
        for w in ["abbaccababcab", "bbcca", "cc", "aababbabbabbccbabba"] {
            if partial.reached_state_from(0, w).unwrap() < 1 {
                panic!("Word {} misclassified", w);
            }
        }
    }
}
