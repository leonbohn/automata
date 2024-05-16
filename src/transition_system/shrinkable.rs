use crate::{math::Set, prelude::*};

use self::alphabet::Matches;

use super::StateIndex;

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

    /// Removes the first edge from the transition system that originates in `source` and matches the given
    /// `crate::prelude::Expression`. The call returns a pair consisting of the color and target of the removed edge.
    /// If no suitable edge is present, returns `None`.
    ///
    /// This method expects to identify the edge that should be removed based on its [`crate::prelude::Expression`], for
    /// a method that identifies the edge based on its target, see [`Self::remove_transitions`].
    fn remove_first_matching(
        &mut self,
        source: impl Indexes<Self>,
        matcher: impl Matches<EdgeExpression<Self>>,
    ) -> Option<(EdgeExpression<Self>, EdgeColor<Self>, StateIndex<Self>)>;

    /// Removes **all** transitions from the transition system that originate in `source` and match the given
    /// `symbol`. The call returns a [`Set`] of triples, each consisting of the expression, color, and target of
    /// the removed transition. If no suitable transitions are present, returns `None`.
    #[allow(clippy::type_complexity)]
    fn remove_all_matching(
        &mut self,
        source: impl Indexes<Self>,
        matcher: impl Matches<EdgeExpression<Self>>,
    ) -> Option<Set<(EdgeExpression<Self>, EdgeColor<Self>, StateIndex<Self>)>>;
}
