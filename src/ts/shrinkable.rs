use crate::{Pointed, TransitionSystem};
use automata_core::alphabet::Matcher;

use super::{EdgeExpression, EdgeTuple, StateColor, StateIndex};

/// Encapsulates the ability to remove states, edges, and transitions from a transition system.
pub trait Shrinkable: TransitionSystem {
    /// Removes a state from the transition system and returns the color associated with the removed state.
    /// Returns `None` if the state does not exist.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     core::alphabet::CharAlphabet,
    ///     ts::{Deterministic, ForAlphabet, Shrinkable, Sproutable},
    ///     DTS,
    /// };
    ///
    /// let mut ts = DTS::for_alphabet(CharAlphabet::of_size(2));
    /// let q0 = ts.add_state(false);
    /// let q1 = ts.add_state(true);
    /// let _edge = ts.add_edge((q0, 'a', q1));
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), Some(q1));
    /// assert_eq!(ts.remove_state(q1), Some(true));
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), None);
    /// ```
    fn remove_state(&mut self, state: StateIndex<Self>) -> Option<Self::StateColor>;

    /// Removes all transitions originating in and a given state whose expression is matched by the given [`Matcher`].
    /// Returns a [`Vec`] of [`EdgeTuple`]s that were removed, if the state exists and `None` otherwise.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     core::alphabet::CharAlphabet,
    ///     ts::{Deterministic, ForAlphabet, Shrinkable, Sproutable},
    ///     DTS,
    /// };
    ///
    /// let mut ts = DTS::for_alphabet(CharAlphabet::of_size(2));
    /// let q0 = ts.add_state(false);
    /// let q1 = ts.add_state(true);
    /// let _edge = ts.add_edge((q0, 'a', q1));
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), Some(q1));
    /// assert_eq!(ts.remove_edges_from_matching(q0, 'a').unwrap().len(), 1);
    /// assert_eq!(ts.remove_edges_from_matching(2, 'b'), None);
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), None);
    /// ```
    fn remove_edges_from_matching(
        &mut self,
        source: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<EdgeTuple<Self>>>;

    /// Removes all edges between two states whose expression is matched by the given [`Matcher`].
    /// Returns a [`Vec`] of [`EdgeTuple`]s that were removed, if the states exist and `None` otherwise.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     core::alphabet::CharAlphabet,
    ///     ts::{Deterministic, ForAlphabet, Shrinkable, Sproutable},
    ///     DTS,
    /// };
    ///
    /// let mut ts = DTS::for_alphabet(CharAlphabet::of_size(2));
    /// let q0 = ts.add_state(true);
    /// let q1 = ts.add_state(true);
    ///
    /// let _e0 = ts.add_edge((q0, 'a', q1));
    /// let _e1 = ts.add_edge((q0, 'b', q1));
    ///
    /// assert_eq!(
    ///     ts.remove_edges_between_matching(q0, q1, 'a').unwrap().len(),
    ///     1
    /// );
    /// assert_eq!(
    ///     ts.remove_edges_between_matching(q0, q0, 'a').unwrap().len(),
    ///     0
    /// );
    /// assert_eq!(ts.remove_edges_between_matching(2, q0, 'a'), None);
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), None);
    /// assert_eq!(ts.reached_state_index_from(q0, "b"), Some(q1));
    /// ```
    fn remove_edges_between_matching(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<EdgeTuple<Self>>>;

    /// Removes all edges between two states. Returns a [`Vec`] of [`EdgeTuple`]s that were removed, if the states exist and `None` otherwise.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     core::alphabet::CharAlphabet,
    ///     ts::{Deterministic, ForAlphabet, Shrinkable, Sproutable},
    ///     DTS,
    /// };
    ///
    /// let mut ts = DTS::for_alphabet(CharAlphabet::of_size(3));
    /// let q0 = ts.add_state(true);
    /// let q1 = ts.add_state(true);
    ///
    /// let _e0 = ts.add_edge((q0, 'a', q1));
    /// let _e1 = ts.add_edge((q0, 'b', q1));
    /// let _e2 = ts.add_edge((q0, 'c', q0));
    ///
    /// assert_eq!(ts.remove_edges_between(q0, q1).unwrap().len(), 2);
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), None);
    /// assert_eq!(ts.reached_state_index_from(q0, "b"), None);
    /// assert_eq!(ts.reached_state_index_from(q0, "c"), Some(q0));
    /// ```
    fn remove_edges_between(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
    ) -> Option<Vec<EdgeTuple<Self>>>;

    /// Removes all edges originating in a given state. Returns a [`Vec`] of [`EdgeTuple`]s that were removed,
    /// if the state exists and `None` otherwise.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     core::alphabet::CharAlphabet,
    ///     ts::{Deterministic, ForAlphabet, Shrinkable, Sproutable},
    ///     DTS,
    /// };
    ///
    /// let mut ts = DTS::for_alphabet(CharAlphabet::of_size(2));
    /// let q0 = ts.add_state(true);
    /// let q1 = ts.add_state(false);
    /// let _q2 = ts.add_state(false);
    ///
    /// ts.add_edge((q0, 'a', q1));
    /// ts.add_edge((q0, 'b', q1));
    /// ts.add_edge((q1, 'a', q0));
    ///
    /// assert_eq!(ts.remove_edges_from(q0).unwrap().len(), 2);
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), None);
    /// assert_eq!(ts.reached_state_index_from(q0, "b"), None);
    /// assert_eq!(ts.reached_state_index_from(q1, "a"), Some(q0));
    /// ```
    fn remove_edges_from(&mut self, source: StateIndex<Self>) -> Option<Vec<EdgeTuple<Self>>>;

    /// Removes all edges going into a state. Returns a [`Vec`] of [`EdgeTuple`]s that were removed,
    /// if the state exists and `None` otherwise.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     core::alphabet::CharAlphabet,
    ///     ts::{ForAlphabet, Shrinkable, Sproutable},
    ///     DTS,
    /// };
    ///
    /// let mut ts = DTS::for_alphabet(CharAlphabet::of_size(2));
    /// let q0 = ts.add_state(true);
    /// let q1 = ts.add_state(false);
    ///
    /// ts.add_edge((q0, 'a', q1));
    /// ts.add_edge((q0, 'b', q1));
    /// ts.add_edge((q1, 'a', q1));
    ///
    /// assert_eq!(ts.remove_edges_to(q1).unwrap().len(), 3);
    /// assert_eq!(ts.remove_edges_to(q0).unwrap().len(), 0);
    /// assert_eq!(ts.remove_edges_to(2), None);
    /// ```
    fn remove_edges_to(&mut self, target: StateIndex<Self>) -> Option<Vec<EdgeTuple<Self>>>;

    /// Removes all states that are not reachable from the given state.
    /// Returns the set of all removed state indices with their associated color.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     core::alphabet::CharAlphabet,
    ///     ts::{ForAlphabet, Shrinkable, Sproutable},
    ///     DTS,
    /// };
    ///
    /// let mut ts = DTS::for_alphabet(CharAlphabet::of_size(2));
    /// let q0 = ts.add_state(true);
    /// let q1 = ts.add_state(false);
    /// let q2 = ts.add_state(false);
    ///
    /// ts.add_edge((q0, 'a', q1));
    /// ts.add_edge((q0, 'b', q1));
    /// ts.add_edge((q1, 'a', q1));
    ///
    /// assert_eq!(ts.trim_from(q0), vec![(q2, false)]);
    /// ```
    fn trim_from(&mut self, source: StateIndex<Self>) -> Vec<(StateIndex<Self>, StateColor<Self>)> {
        assert!(self.contains_state_index(source));
        let reachable = self
            .reachable_state_indices_from(source)
            .collect::<Vec<_>>();
        let mut out = Vec::new();
        for q in self.state_indices_vec() {
            if !reachable.contains(&q) {
                let c = self.remove_state(q).expect("We know this exists");
                out.push((q, c));
            }
        }
        out
    }

    /// Removes all states that are not reachable from the initial state and returns the set of
    /// all removed state indices with their associated color. See [`Self::trim_from`] for an example.
    fn trim(&mut self) -> Vec<(StateIndex<Self>, StateColor<Self>)>
    where
        Self: Pointed,
    {
        self.trim_from(self.initial())
    }
}

#[cfg(test)]
mod tests {
    use crate::representation::CollectTs;
    use crate::ts::{ForAlphabet, Shrinkable, Sproutable};
    use crate::{TransitionSystem, DTS};
    use automata_core::alphabet::CharAlphabet;
    use automata_core::Void;

    #[test]
    fn shrink_to_reachable() {
        let mut ts = DTS::for_alphabet(CharAlphabet::of_size(1));
        let q0 = ts.add_state(Void);
        let q1 = ts.add_state(Void);
        let q2 = ts.add_state(Void);
        let q3 = ts.add_state(Void);
        let q4 = ts.add_state(Void);
        let q5 = ts.add_state(Void);

        ts.add_edge((q1, 'a', 2, q0));
        ts.add_edge((q0, 'a', 2, q3));
        ts.add_edge((q3, 'a', 0, q5));
        ts.add_edge((q5, 'a', 3, q4));
        ts.add_edge((q4, 'a', 3, q2));
        ts.add_edge((q2, 'a', 0, q4));

        let mut mm = ts.with_initial(q0).collect_mealy();
        mm.trim_from(q0);
        assert_eq!(mm.size(), 5);
    }
}
