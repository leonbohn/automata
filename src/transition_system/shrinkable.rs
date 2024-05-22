use crate::prelude::*;

use self::alphabet::Matcher;

use super::EdgeTuple;

/// Encapsulates the ability to remove states, edges, and transitions from a transition system.
pub trait Shrinkable: TransitionSystem {
    /// Removes a state from the transition system and returns the color associated with the removed state.
    /// Returns `None` if the state does not exist.
    ///
    /// # Example
    /// ```
    /// use automata::prelude::*;
    ///
    /// let mut ts = EdgeListsDeterministic::for_alphabet(alphabet!(simple 'a', 'b'));
    /// let q0 = ts.add_state(false);
    /// let q1 = ts.add_state(true);
    /// let edge = ts.add_edge((q0, 'a', q1));
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
    /// use automata::prelude::*;
    ///
    /// let mut ts = EdgeListsDeterministic::for_alphabet(alphabet!(simple 'a', 'b'));
    /// let q0 = ts.add_state(false);
    /// let q1 = ts.add_state(true);
    /// let edge = ts.add_edge((q0, 'a', q1));
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
    /// use automata::prelude::*;
    ///
    /// let mut ts = EdgeListsDeterministic::for_alphabet(alphabet!(simple 'a', 'b'));
    /// let q0 = ts.add_state(true);
    /// let q1 = ts.add_state(true);
    ///
    /// let e0 = ts.add_edge((q0, 'a', q1));
    /// let e1 = ts.add_edge((q0, 'b', q1));
    ///
    /// assert_eq!(ts.remove_edges_between_matching(q0, q1, 'a').unwrap().len(), 1);
    /// assert_eq!(ts.remove_edges_between_matching(q0, q0, 'a').unwrap().len(), 0);
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
    /// use automata::prelude::*;
    ///
    /// let mut ts = EdgeListsDeterministic::for_alphabet(alphabet!(simple 'a', 'b', 'c'));
    /// let q0 = ts.add_state(true);
    /// let q1 = ts.add_state(true);
    ///
    /// let e0 = ts.add_edge((q0, 'a', q1));
    /// let e1 = ts.add_edge((q0, 'b', q1));
    /// let e2 = ts.add_edge((q0, 'c', q0));
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
    /// use automata::prelude::*;
    ///
    /// let mut ts = EdgeListsDeterministic::for_alphabet(alphabet!(simple 'a', 'b'));
    /// let q0 = ts.add_state(true);
    /// let q1 = ts.add_state(false);
    /// let q2 = ts.add_state(false);
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
    /// use automata::prelude::*;
    ///
    /// let mut ts = EdgeListsDeterministic::for_alphabet(alphabet!(simple 'a', 'b'));
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
}
