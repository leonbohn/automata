use crate::prelude::*;

mod acceptance_type;
pub use acceptance_type::OmegaAcceptanceType;

#[macro_use]
mod moore;
pub use moore::{IntoMooreMachine, MooreLike, MooreMachine};

#[macro_use]
mod mealy;
pub use mealy::{IntoMealyMachine, MealyLike, MealyMachine};

mod dfa;
pub use dfa::{DFALike, IntoDFA, DFA};

mod dpa;
pub use dpa::{DPALike, IntoDPA, MinEven, DPA};

mod dba;
pub use dba::{DBALike, IntoDBA, DBA};

#[allow(missing_docs)]
mod omega;
pub use omega::{
    AcceptanceMask, DeterministicOmegaAutomaton, OmegaAcceptanceCondition, OmegaAutomaton,
};

mod acceptor;
pub use acceptor::Automaton;

mod with_initial;
pub use with_initial::Initialized;

/// This trait is implemented by acceptance conditions for finite words.
pub trait FiniteSemantics<Q, C> {
    /// The type of output that this semantic produces.
    type Output;
    /// Compute the output for the given finite run.
    fn finite_semantic<R>(&self, run: R) -> Self::Output
    where
        R: FiniteRun<StateColor = Q, EdgeColor = C>;
}

/// This trait is implemented by acceptance conditions for omega words.
pub trait OmegaSemantics<Q, C> {
    /// The type of output that this semantic produces.
    type Output;
    /// Compute the output for the given omega run.
    fn omega_semantic<R>(&self, run: R) -> Self::Output
    where
        R: OmegaRun<StateColor = Q, EdgeColor = C>;
}

/// Iterator over the accepting states of a [`TransitionSystem`] that have a certain coloring.
pub struct StatesWithColor<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    iter: Ts::StateIndices<'a>,
    color: Ts::StateColor,
}

impl<'a, Ts: TransitionSystem> StatesWithColor<'a, Ts> {
    /// Creates a new instance for the given transition system and color.
    pub fn new(ts: &'a Ts, color: Ts::StateColor) -> Self {
        Self {
            iter: ts.state_indices(),
            ts,
            color,
        }
    }
}

impl<'a, Ts: TransitionSystem> Clone for StatesWithColor<'a, Ts> {
    fn clone(&self) -> Self {
        Self {
            ts: self.ts,
            iter: self.ts.state_indices(),
            color: self.color.clone(),
        }
    }
}

impl<'a, Ts: TransitionSystem<StateColor = bool>> Iterator for StatesWithColor<'a, Ts> {
    type Item = Ts::StateIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .find(|&index| self.ts.state_color(index).unwrap() == self.color)
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn mealy_color_or_below() {
        let mut mm: MooreMachine<CharAlphabet, usize> =
            MooreMachine::new_for_alphabet(alphabet!(simple 'a', 'b'));
        let a = mm.add_state(0usize);
        let b = mm.add_state(1usize);
        let c = mm.add_state(1usize);
        let d = mm.add_state(0usize);
        mm.add_edge(a, 'a', b, Void);
        mm.add_edge(a, 'b', c, ());
        mm.add_edge(b, 'a', c, ());
        mm.add_edge(b, 'b', c, ());
        mm.add_edge(c, 'a', d, ());
        mm.add_edge(c, 'b', c, ());
        mm.add_edge(d, 'a', d, ());
        mm.add_edge(d, 'b', d, ());

        let dfas = mm.decompose_dfa();
        let dfa1 = &dfas[1];
        let dfa0 = &dfas[0];

        println!("{:?}", dfa0);
        assert!(dfa1.accepts(""));
        assert!(dfa1.accepts("b"));
        assert!(!dfa0.accepts("b"));
        assert!(dfa0.accepts("ba"));
    }

    #[test]
    fn dbas() {
        let mut dba = super::DBA::new_for_alphabet(CharAlphabet::from_iter(['a', 'b']));
        let q0 = dba.add_state(());
        let q1 = dba.add_state(Void);

        let _e0 = dba.add_edge(q0, 'a', q1, true);
        let _e1 = dba.add_edge(q0, 'b', q0, false);
        let _e2 = dba.add_edge(q1, 'a', q1, true);
        let _e3 = dba.add_edge(q1, 'b', q0, false);
        assert!(dba.accepts(ReducedOmegaWord::periodic("abb")));
        assert!(!dba.accepts(ReducedOmegaWord::periodic("b")));
        assert!(dba.accepts(upw!("a")));
        assert!(!dba.accepts(upw!("b")));

        assert!(!dba.dba_is_empty());
        println!("{:?}", dba.dba_give_word());

        println!("{:?}", &dba);
    }

    #[test]
    fn dfas_and_boolean_operations() {
        let mut dfa = super::DFA::new_for_alphabet(CharAlphabet::new(['a', 'b']));
        let s0 = dfa.add_state(true);
        let s1 = dfa.add_state(false);
        let _e0 = dfa.add_edge(s0, 'a', s1, Void);
        let _e1 = dfa.add_edge(s0, 'b', s0, Void);
        let _e2 = dfa.add_edge(s1, 'a', s1, Void);
        let _e3 = dfa.add_edge(s1, 'b', s0, Void);

        assert!(!dfa.is_empty_language());
        assert_eq!(dfa.give_word(), Some(vec![]));

        let _dfb = dfa.clone();

        assert!(dfa.accepts("ababab"));
        assert!(!dfa.accepts("a"));

        let notdfa = dfa.as_ref().negation().into_dfa();
        assert!(!notdfa.accepts("ababab"));
        assert!(notdfa.accepts("a"));

        let intersection = dfa.as_ref().intersection(&notdfa).into_dfa();
        assert!(!intersection.accepts("ababab"));
        assert!(!intersection.accepts("a"));

        let union = dfa.as_ref().union(&notdfa).into_dfa();
        assert!(union.accepts("ababab"));
        assert!(union.accepts("a"));
    }
}
