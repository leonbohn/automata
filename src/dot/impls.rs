use super::{DotStateAttribute, DotStyle, DotTransitionAttribute, Dottable};
use crate::DTS;
use crate::automaton::{
    Automaton, BuchiCondition, MealySemantics, MinEvenParityCondition, MooreSemantics,
    OmegaAcceptanceCondition, ReachabilityCondition,
};
use crate::ts::{EdgeOf, StateIndex, States};
use crate::{Color, Pointed, Show, TransitionSystem, alphabet::Alphabet};

/// All automata are drawn through the [`DotStyle`] of their acceptance condition.
impl<T: States, Z: DotStyle<T>> Dottable for Automaton<T, Z> {
    fn dot_name(&self) -> Option<String> {
        self.acceptance().dot_name()
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: EdgeOf<'a, Self>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        self.acceptance().dot_transition_attributes(self.ts(), t)
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        self.acceptance().dot_state_attributes(self.ts(), idx)
    }
}

impl<T: States<StateColor = bool>> DotStyle<T> for ReachabilityCondition {
    fn dot_name(&self) -> Option<String> {
        Some("DFA".into())
    }

    fn dot_state_attributes(&self, ts: &T, q: StateIndex<T>) -> Vec<DotStateAttribute> {
        let shape = if ts.state_color(q).is_some_and(|accepting| *accepting) {
            "doublecircle"
        } else {
            "circle"
        };
        vec![
            DotStateAttribute::Shape(shape.into()),
            DotStateAttribute::Label(format!("q{q:?}")),
        ]
    }

    fn dot_transition_attributes(&self, _ts: &T, t: EdgeOf<'_, T>) -> Vec<DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(t.expression().show())]
    }
}

impl<T: States> DotStyle<T> for MooreSemantics {
    fn dot_name(&self) -> Option<String> {
        Some("Moore".into())
    }

    fn dot_state_attributes(&self, ts: &T, q: StateIndex<T>) -> Vec<DotStateAttribute> {
        let color = ts
            .state_color(q)
            .map(|c| format!(" | {c:?}"))
            .unwrap_or_default();
        vec![DotStateAttribute::Label(format!("q{q:?}{color}"))]
    }

    fn dot_transition_attributes(&self, _ts: &T, t: EdgeOf<'_, T>) -> Vec<DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(t.expression().show())]
    }
}

/// Styles that label an edge with its expression and color and draw plain states.
macro_rules! edge_colored_style {
    ($($cond:ty => $name:literal),*) => {$(
        impl<T: States> DotStyle<T> for $cond {
            fn dot_name(&self) -> Option<String> {
                Some($name.into())
            }
        }
    )*};
}
edge_colored_style!(
    MealySemantics => "Mealy",
    MinEvenParityCondition => "DPA",
    BuchiCondition => "DBA",
    OmegaAcceptanceCondition => "Omega"
);

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
            "{}|{}",
            self.dot_state_ident(idx),
            self.state_color(idx)
                .map(|c| format!("{c:?}"))
                .unwrap_or_default()
        ))]
    }
}
