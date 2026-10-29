mod recolor;
pub use recolor::{
    ColorFn, DefaultIfMissing, EdgeFn, EdgeRecolor, EraseColors, EraseEdgeColors, EraseStateColors,
    Keep, Provided, ProvidesStateColor, Recolor, RecolorEdges, StateColorFn, StateRecolor,
    UniformColor,
};

mod product;
pub use product::*;

mod restricted;
pub use restricted::*;

mod subset;
pub use subset::SubsetConstruction;

mod reachable;
pub use reachable::ReachablePart;

mod reverse;
pub use reverse::Reversed;

mod quotient;
pub use quotient::{Quotient, QuotientEdgesFrom};

#[cfg(test)]
mod tests {
    use crate::automaton::DFA;
    use crate::representation::IntoTs;
    use crate::ts::Deterministic;
    use crate::ts::operations::{Product, ProductIndex};
    use crate::{Pointed, TransitionSystem};

    #[test]
    fn product() {
        let dfa = DFA::builder()
            .with_state_colors([true, false])
            .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 0)])
            .into_dfa(0);

        let dfb = DFA::builder()
            .with_state_colors([true, true])
            .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 0)])
            .into_dfa(0);

        let xxx = dfa.ts_product(dfb);
        assert_eq!(xxx.reached_state("abb"), Some(ProductIndex(0, 0)));
        assert_eq!(xxx.run("aa").reached_state_color(), Some((false, true)));

        let yyy = xxx
            .clone()
            .reachable_part()
            .map_state_colors(|(a, b)| a || b)
            .into_dfa();
        assert_eq!(yyy.run("aa").reached_state_color(), Some(true));
    }
}
