pub mod product {
    use crate::game::{Game, IntoGame};

    pub struct Product<G, H> {
        g: G,
        h: H,
    }

    impl<G: Game, H: Game> IntoGame<(G::V, H::V), (G::E, H::E)> for Product<G, H> {
        type IntoG = crate::PetGame<(G::V, H::V), (G::E, H::E)>;

        fn into_game(self) -> Self::IntoG {
            todo!()
        }
    }
}
