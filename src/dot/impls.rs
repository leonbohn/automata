use super::{DotStateAttribute, DotTransitionAttribute, Dottable};
use crate::DTS;
use crate::Void;
use crate::automaton::{DFA, DPA, MealyMachine, MooreMachine};
use crate::ts::EdgeOf;
use crate::ts::States;
use crate::ts::{Deterministic, StateColor, StateIndex};
use crate::{Color, Int, Pointed, Show, TransitionSystem, alphabet::Alphabet};

impl<A: Alphabet> Dottable for DFA<DTS<A, bool, Void>>
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
        t: EdgeOf<'a, Self>,
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
impl<A: Alphabet, Q: Color, C: Color> Dottable for crate::RightCongruence<DTS<A, Q, C>>
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
        t: EdgeOf<'a, Self>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        [DotTransitionAttribute::Label(format!(
            "{:?}|{:?}",
            t.expression(),
            t.color()
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

impl<M> Dottable for MooreMachine<M>
where
    M: Deterministic + States,
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
        t: EdgeOf<'a, Self>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(t.expression().show())]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }
}

impl<M> Dottable for MealyMachine<M>
where
    M: Deterministic + States,
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
        t: EdgeOf<'a, Self>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(format!(
            "{}|{:?}",
            t.expression().show(),
            t.color()
        ))]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }
}

impl<D> Dottable for DPA<D>
where
    D: Deterministic<EdgeColor = Int> + States,
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
        t: EdgeOf<'a, Self>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(format!(
            "{}|{}",
            t.expression().show(),
            t.color().show()
        ))]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }
}
