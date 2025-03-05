use automata_core::Void;

mod map;
pub use map::*;

mod product;
pub use product::*;

mod restricted;
pub use restricted::*;

mod subset;
pub use subset::SubsetConstruction;

mod reverse;
pub use reverse::Reversed;

mod quotient;
pub use quotient::{Quotient, QuotientEdgesFrom, QuotientTransition};

mod with_state_color;
pub use with_state_color::{DefaultIfMissing, ProvidesStateColor, UniformColor, WithStateColor};

use super::{EdgeColor, StateColor};

/// Type alias for the transition system that results from erasing all
/// colors, c.f. [`super::TransitionSystem::erase_colors`].
pub type EraseColors<Ts> =
    MapEdgeColor<MapStateColor<Ts, fn(StateColor<Ts>) -> Void>, fn(EdgeColor<Ts>) -> Void>;

#[cfg(test)]
mod tests {
    use crate::TransitionSystem;
    use crate::automaton::DFA;
    use crate::representation::IntoTs;
    use crate::ts::Deterministic;
    use crate::ts::operations::{Product, ProductIndex};

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
        assert_eq!(xxx.reached_state_index("abb"), Some(ProductIndex(0, 0)));
        assert_eq!(xxx.reached_state_color("aa"), Some((false, true)));

        let yyy = xxx.clone().map_state_colors(|(a, b)| a || b).into_dfa();
        assert_eq!(yyy.reached_state_color("aa"), Some(true));
    }
}
