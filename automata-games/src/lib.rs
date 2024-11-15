mod game;
mod operations;

use petgraph::prelude::*;

pub type PetGame<V, E, Id> = petgraph::graph::DiGraph<V, E, Id>;
