use std::{collections::VecDeque, hash::Hash};

use itertools::Itertools;

use crate::prelude::*;

pub struct StateSet<T: TransitionSystem> {
    states: math::OrderedSet<StateIndex<T>>,
    colors: Vec<StateColor<T>>,
}

impl<T: TransitionSystem> Eq for StateSet<T> {}

impl<T: TransitionSystem> PartialEq for StateSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.states == other.states && self.colors == other.colors
    }
}

impl<T: TransitionSystem> std::fmt::Debug for StateSet<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{{}}}[{}]",
            self.states.iter().map(|q| q.show()).join(", "),
            self.colors.iter().map(|c| format!("{:?}", c)).join(", ")
        )
    }
}

impl<T: TransitionSystem> Clone for StateSet<T> {
    fn clone(&self) -> Self {
        Self {
            states: self.states.clone(),
            colors: self.colors.clone(),
        }
    }
}

impl<T: TransitionSystem> Hash for StateSet<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.states.hash(state);
        self.colors.hash(state);
    }
}

impl<T: TransitionSystem> StateSet<T> {
    pub fn new<I: IntoIterator<Item = StateIndex<T>>>(states: I, ts: &T) -> Self {
        let states = states.into_iter().collect::<math::OrderedSet<_>>();
        let colors = states
            .iter()
            .map(|&state| ts.state_color(state).unwrap())
            .cloned()
            .collect();
        Self { states, colors }
    }
}

pub fn subset_construction_from<T: TransitionSystem, I: IntoIterator<Item = StateIndex<T>>>(
    ts: T,
    initial_states: I,
) -> DTS<T::Alphabet, StateSet<T>, Vec<EdgeColor<T>>> {
    let mut dts = DTS::for_alphabet(ts.alphabet().clone());
    let mut queue = VecDeque::with_capacity(ts.hint_size().0);

    let initial_state = StateSet::new(initial_states, &ts);
    let initial_id = dts.add_state(initial_state);
    queue.push_back(initial_id);

    todo!()
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test_log::test]
    fn subset_construction() {
        let nts = LinkedListNondeterministic::builder()
            .default_color(false)
            .with_transitions([
                (0, 'a', 0),
                (0, 'a', 1),
                (0, 'b', 1),
                (1, 'b', 1),
                (1, 'a', 0),
            ])
            .into_dts()
            .with_initial(0);

        let dts = nts.subset_construction();

        for idx in dts.reachable_state_indices() {
            println!("idx: {}[{:?}]", idx, dts.state_color(idx));
        }
        assert_eq!(dts.reachable_state_indices().count(), 3);
        println!("first");
        assert_eq!(dts.state_indices().count(), 3);
        println!("second");
        assert_eq!(dts.trim_collect().0.size(), 3);
    }
}
