use super::{DotStateAttribute, DotTransitionAttribute, Dottable};
use crate::automaton::{DFA, IntoDPA, IntoMealyMachine, IntoMooreMachine};
use crate::ts::{Deterministic, IsEdge, StateColor, StateIndex};
use crate::{Color, Int, Pointed, Show, TransitionSystem, alphabet::Alphabet};

impl<A: Alphabet> Dottable for DFA<A>
where
    StateIndex<Self>: Show,
{
    fn dot_name(&self) -> Option<String> {
        Some("DFA".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{}", idx.show())
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        [DotTransitionAttribute::Label(t.expression().show())].into_iter()
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute>
    where
        (String, StateColor<Self>): Show,
    {
        let shape = if *self.state_color(idx).unwrap() {
            "doublecircle"
        } else {
            "circle"
        };
        vec![
            DotStateAttribute::Shape(shape.into()),
            DotStateAttribute::Label(self.dot_state_ident(idx)),
        ]
    }
}
impl<A: Alphabet, Q: Color, C: Color> Dottable for crate::RightCongruence<A, Q, C>
where
    StateIndex<Self>: Show,
{
    fn dot_name(&self) -> Option<String> {
        Some("Congruence".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("c{}", idx.show())
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        [DotTransitionAttribute::Label(format!(
            "{:?}|{:?}",
            t.expression(),
            IsEdge::color(&t)
        ))]
        .into_iter()
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        vec![DotStateAttribute::Label(format!(
            "{}|{:?}",
            self.dot_state_ident(idx),
            self.state_color(idx).unwrap()
        ))]
    }
}

impl<M> Dottable for IntoMooreMachine<M>
where
    M: Deterministic,
{
    fn dot_name(&self) -> Option<String> {
        Some("DPA".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        let color = self
            .state_color(idx)
            .map(|c| format!(" | {c:?}"))
            .unwrap_or("".to_string());
        vec![DotStateAttribute::Label(format!(
            "{}{color}",
            self.dot_state_ident(idx)
        ))]
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(t.expression().show())]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }
}

impl<M> Dottable for IntoMealyMachine<M>
where
    M: Deterministic,
{
    fn dot_name(&self) -> Option<String> {
        Some("DPA".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        if self.initial() == idx {
            vec![DotStateAttribute::Label(format!(
                "->{}",
                self.dot_state_ident(idx)
            ))]
        } else {
            vec![DotStateAttribute::Label(self.dot_state_ident(idx))]
        }
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(format!(
            "{}|{:?}",
            t.expression().show(),
            IsEdge::color(&t)
        ))]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }
}

impl<D> Dottable for IntoDPA<D>
where
    D: Deterministic<EdgeColor = Int>,
{
    fn dot_name(&self) -> Option<String> {
        Some("DPA".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        vec![DotStateAttribute::Label(self.dot_state_ident(idx))]
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(format!(
            "{}|{}",
            t.expression().show(),
            IsEdge::color(&t).show()
        ))]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }
}
