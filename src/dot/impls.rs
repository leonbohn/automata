use super::{DotStateAttribute, DotStyle, DotTransitionAttribute, Dottable};
use crate::DTS;
use crate::automaton::{
    Automaton, BuchiCondition, CoBuchiCondition, Existential, MaxEvenParityCondition,
    MaxOddParityCondition, MealySemantics, MinEvenParityCondition, MinOddParityCondition,
    MooreSemantics, MullerCondition, OmegaAcceptanceCondition, RabinCondition, RabinPair,
    ReachabilityCondition, StreettCondition,
};
use crate::ts::{EdgeColor, EdgeOf, StateIndex, States};
use crate::{Color, Pointed, TransitionSystem, alphabet::Alphabet};
use itertools::Itertools;

/// All automata are drawn through the [`DotStyle`] of their acceptance condition.
impl<T: States, Z: DotStyle<T>> Dottable for Automaton<T, Z> {
    fn dot_name(&self) -> Option<String> {
        self.acceptance().dot_name()
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_header_statements(&self) -> impl IntoIterator<Item = String> {
        self.acceptance().dot_header_statements()
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

/// Double circles for the accepting states, circles for the others.
fn final_state_attributes<T: States<StateColor = bool>>(
    ts: &T,
    q: StateIndex<T>,
) -> Vec<DotStateAttribute> {
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

/// The styles of DFAs and NFAs, which only differ in their name.
macro_rules! final_state_style {
    ($($cond:ty => $name:literal),*) => {$(
        impl<T: States<StateColor = bool>> DotStyle<T> for $cond {
            fn dot_name(&self) -> Option<String> {
                Some($name.into())
            }

            fn dot_state_attributes(&self, ts: &T, q: StateIndex<T>) -> Vec<DotStateAttribute> {
                final_state_attributes(ts, q)
            }

            fn dot_transition_attributes(
                &self,
                _ts: &T,
                t: EdgeOf<'_, T>,
            ) -> Vec<DotTransitionAttribute> {
                vec![DotTransitionAttribute::Label(t.expression().to_string())]
            }
        }
    )*};
}
final_state_style!(ReachabilityCondition => "DFA", Existential<ReachabilityCondition> => "NFA");

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
        vec![DotTransitionAttribute::Label(t.expression().to_string())]
    }
}

/// Styles that label an edge with its expression and color and draw plain states. The optional
/// second name is the one for the nondeterministic automata with the same condition.
macro_rules! edge_colored_style {
    ($($cond:ty => $name:literal $(, $nondeterministic:literal)?);*) => {$(
        impl<T: States> DotStyle<T> for $cond {
            fn dot_name(&self) -> Option<String> {
                Some($name.into())
            }
        }
        $(
            impl<T: States> DotStyle<T> for Existential<$cond> {
                fn dot_name(&self) -> Option<String> {
                    Some($nondeterministic.into())
                }
            }
        )?
    )*};
}
edge_colored_style!(
    MealySemantics => "Mealy";
    MinEvenParityCondition => "DPA", "NPA";
    MaxEvenParityCondition => "DPA", "NPA";
    MinOddParityCondition => "DPA", "NPA";
    MaxOddParityCondition => "DPA", "NPA";
    BuchiCondition => "DBA", "NBA";
    CoBuchiCondition => "DCA", "NCA";
    OmegaAcceptanceCondition => "Omega"
);

/// The statement for a node that only holds the text of the acceptance condition. A node rather
/// than a graph `label`, because the native renderer ignores the latter.
fn legend(text: &str) -> String {
    format!("acceptance [shape=\"plaintext\", label=\"{text}\"]")
}

/// The statement that lists the pairs of a Rabin or Streett condition.
fn pairs_label<'a, C: Color + Ord + 'a>(
    kind: &str,
    pairs: impl Iterator<Item = &'a RabinPair<C>>,
) -> String {
    let pairs = pairs
        .map(|pair| format!("(fin {:?}, inf {:?})", pair.fin(), pair.inf()))
        .join("; ");
    legend(&format!("{kind}: {pairs}"))
}

fn rabin_label<C: Color + Ord>(condition: &RabinCondition<C>) -> String {
    pairs_label("Rabin", condition.pairs())
}

fn streett_label<C: Color + Ord>(condition: &StreettCondition<C>) -> String {
    pairs_label("Streett", condition.pairs())
}

/// The statement that lists the sets of a Muller condition.
fn muller_label<C: Color + Ord + std::hash::Hash>(condition: &MullerCondition<C>) -> String {
    let sets = condition
        .sets()
        .iter()
        .map(|set| format!("{:?}", set.iter().collect::<Vec<_>>()))
        .join(", ");
    legend(&format!("Muller: {sets}"))
}

/// Rabin, Streett and Muller conditions and their nondeterministic variants: the edges show their
/// color and the condition is written in a separate node.
macro_rules! condition_label_style {
    ($($cond:ident => $name:literal, $nondeterministic:literal, $label:ident);*) => {$(
        impl<T: States> DotStyle<T> for $cond<EdgeColor<T>>
        where
            EdgeColor<T>: Ord + std::hash::Hash,
        {
            fn dot_name(&self) -> Option<String> {
                Some($name.into())
            }

            fn dot_header_statements(&self) -> Vec<String> {
                vec![$label(self)]
            }
        }

        impl<T: States> DotStyle<T> for Existential<$cond<EdgeColor<T>>>
        where
            EdgeColor<T>: Ord + std::hash::Hash,
        {
            fn dot_name(&self) -> Option<String> {
                Some($nondeterministic.into())
            }

            fn dot_header_statements(&self) -> Vec<String> {
                vec![$label(&self.0)]
            }
        }
    )*};
}
condition_label_style!(
    RabinCondition => "DRA", "NRA", rabin_label;
    StreettCondition => "DSA", "NSA", streett_label;
    MullerCondition => "DMA", "NMA", muller_label
);

impl<A: Alphabet, Q: Color, C: Color> Dottable for crate::RightCongruence<DTS<A, Q, C>>
where
    StateIndex<Self>: std::fmt::Display,
{
    fn dot_name(&self) -> Option<String> {
        Some("Congruence".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("c{}", idx)
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
