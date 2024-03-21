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

#[cfg(test)]
mod tests {
    use crate::prelude::*;

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
