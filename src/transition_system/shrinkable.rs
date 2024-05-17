use crate::prelude::*;

use self::alphabet::Matcher;

use super::{EdgeRef, EdgeTuple};

/// Encapsulates the ability to remove states, edges, and transitions from a transition system.
pub trait Shrinkable: TransitionSystem {
    /// Removes a state from the transition system and returns the color associated with the removed state.
    /// Returns `None` if the state does not exist.
    ///
    /// # Example
    /// ```
    /// use automata::prelude::*;
    ///
    /// let mut ts = DTS::for_alphabet(alphabet!(simple 'a', 'b'));
    /// let q0 = ts.add_state(false);
    /// let q1 = ts.add_state(true);
    /// let edge = ts.add_edge((q0, 'a', q1));
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), Some(q1));
    /// assert_eq!(ts.remove_state(q1), Some(true));
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), None);
    /// ```
    fn remove_state<Idx: Indexes<Self>>(&mut self, state: Idx) -> Option<Self::StateColor>;

    /// Removes all transitions originating in and a given state whose expression is matched by the given [`Matcher`].
    /// Returns a [`Set`] of [`EdgeTuple`]s that were removed, if the state exists and `None` otherwise.
    ///
    /// # Example
    /// ```
    /// use automata::prelude::*;
    ///
    /// let mut ts = DTS::for_alphabet(alphabet!(simple 'a', 'b'));
    /// let q0 = ts.add_state(false);
    /// let q1 = ts.add_state(true);
    /// let edge = ts.add_edge((q0, 'a', q1));
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), Some(q1));
    /// assert_eq!(ts.remove_all_edges_matching(q0, 'a'), Some(vec![('a', None, q1)]));
    /// assert_eq!(ts.reached_state_index_from(q0, "a"), None);
    /// ```
    fn remove_edges_from_matching(
        &mut self,
        source: impl Indexes<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<EdgeTuple<Self>>>;

    fn remove_edges_between_matching(
        &mut self,
        source: impl Indexes<Self>,
        target: impl Indexes<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<EdgeTuple<Self>>>;

    fn remove_edges_between(
        &mut self,
        source: impl Indexes<Self>,
        target: impl Indexes<Self>,
    ) -> Option<Vec<EdgeTuple<Self>>>;

    fn remove_edges_from(&mut self, source: impl Indexes<Self>) -> Option<Vec<EdgeTuple<Self>>>;

    fn remove_edge<'a>(&'a mut self, edge: EdgeRef<'a, Self>) -> Option<EdgeTuple<Self>>;
}
