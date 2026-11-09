//! Python classes for parity games, one per parity condition. Games have no alphabet, so there is
//! no `Prop` variant.

use automata::{
    Int,
    game::{
        Arena, GameError, MaxEvenParityGame, MaxOddParityGame, MinEvenParityGame, MinOddParityGame,
        ParityGame, Player,
    },
    ts::{DenseId, StateId, States},
};
use pyo3::{exceptions::PyValueError, prelude::*};
use pyo3_stub_gen::derive::{gen_stub_pyclass, gen_stub_pymethods};

use crate::error::PyError;

/// Parses the name of a player, `"eve"` or `"adam"`.
fn player(name: &str) -> PyResult<Player> {
    match name {
        "eve" => Ok(Player::Eve),
        "adam" => Ok(Player::Adam),
        _ => Err(PyValueError::new_err(format!(
            "unknown player {name:?}, expected \"eve\" or \"adam\""
        ))),
    }
}

fn player_name(player: Player) -> &'static str {
    match player {
        Player::Eve => "eve",
        Player::Adam => "adam",
    }
}

/// The letter game of the automaton `automaton`, see [`ParityGame::letter_game`], and the vertex
/// of its initial state.
pub fn letter_game<T, S>(
    automaton: &automata::automaton::Automaton<T, S>,
    chooser: &str,
) -> PyResult<(PyMinEvenParityGame, u32)>
where
    T: automata::TransitionSystem<EdgeColor = Int> + States,
    automata::automaton::Automaton<T, S>: automata::ts::Pointed<StateIndex = T::StateIndex>,
{
    let (game, vertices) = MinEvenParityGame::letter_game(automaton.ts(), player(chooser)?);
    let initial = vertices
        .get(&automata::ts::Pointed::initial(automaton))
        .map(|q| q.into_usize() as u32)
        .ok_or_else(|| PyValueError::new_err("the initial state is not a state"))?;
    Ok((PyMinEvenParityGame(game), initial))
}

/// Checks that `v` is one of the vertices of `game` and returns it as a state of the arena.
fn vertex<C>(game: &ParityGame<Arena, C>, v: u32) -> PyResult<StateId> {
    let n = game.arena().state_count();
    if (v as usize) < n {
        Ok(StateId::from(v))
    } else {
        Err(PyValueError::new_err(format!(
            "vertex {v} does not exist, there are {n} vertices"
        )))
    }
}

/// The winner of each vertex; vertices are numbered like the states of the arena.
fn winners_of(
    solution: &automata::game::Solution<StateId>,
    n: usize,
) -> PyResult<Vec<&'static str>> {
    (0..n as u32)
        .map(|v| {
            solution
                .winner(StateId::from(v))
                .map(player_name)
                .ok_or_else(|| PyValueError::new_err("vertex without a winner"))
        })
        .collect()
}

macro_rules! parity_game_class {
    ($name:ident, $py_name:literal, $rust:ident, $doc:expr) => {
        #[doc = $doc]
        #[gen_stub_pyclass]
        #[pyclass(name = $py_name, module = "automata._automata")]
        #[derive(Clone)]
        pub struct $name($rust);

        #[gen_stub_pymethods]
        #[pymethods]
        impl $name {
            /// Creates a game with the given `vertices`, pairs `(owner, priority)` with owner
            /// `"eve"` or `"adam"` and a priority from 0 to 255, and `edges`, pairs
            /// `(source, target)` of vertices. The vertices are numbered `0, 1, ...` in the order
            /// of `vertices`. Raises `ValueError` for an unknown player or a vertex that does not
            /// exist.
            #[new]
            #[pyo3(signature = (vertices = Vec::new(), edges = Vec::new()))]
            fn new(vertices: Vec<(String, Int)>, edges: Vec<(u32, u32)>) -> PyResult<Self> {
                let mut game = Self($rust::new());
                for (owner, priority) in vertices {
                    game.add_vertex(&owner, priority)?;
                }
                for (source, target) in edges {
                    game.add_edge(source, target)?;
                }
                Ok(game)
            }

            /// Reads a game in the PGSolver format, see the Rust documentation of
            /// `ParityGame.from_pgsolver`. PGSolver and Oink use max-even priorities. Raises
            /// `GameError` if the text is not a valid game.
            #[staticmethod]
            fn from_pgsolver(text: &str) -> PyResult<Self> {
                $rust::from_pgsolver(text)
                    .map(Self)
                    .map_err(|e| PyError(e.into()).into())
            }

            /// Writes the game in the PGSolver format; vertex `i` has id `i`.
            fn to_pgsolver(&self) -> String {
                self.0.to_pgsolver()
            }

            /// Adds a vertex owned by `owner` (`"eve"` or `"adam"`) with the given priority and
            /// returns its number.
            fn add_vertex(&mut self, owner: &str, priority: Int) -> PyResult<u32> {
                Ok(self.0.add_vertex(player(owner)?, priority).into_usize() as u32)
            }

            /// Adds an edge between two existing vertices.
            fn add_edge(&mut self, source: u32, target: u32) -> PyResult<()> {
                let (source, target) = (vertex(&self.0, source)?, vertex(&self.0, target)?);
                self.0.add_edge(source, target);
                Ok(())
            }

            /// Solves the game and returns, for every vertex, its winner: `"eve"` or `"adam"`.
            ///
            /// Raises `GameError` if some vertex has no successor.
            fn solve(&self, py: Python<'_>) -> PyResult<Vec<&'static str>> {
                let solution = py
                    .detach(|| self.0.solve())
                    .map_err(|e: GameError| PyError(e.into()))?;
                winners_of(&solution, self.__len__())
            }

            /// Like `solve`, but with Zielonka's algorithm, which is slower and serves as a
            /// reference.
            fn solve_zielonka(&self, py: Python<'_>) -> PyResult<Vec<&'static str>> {
                let solution = py
                    .detach(|| self.0.solve_zielonka())
                    .map_err(|e: GameError| PyError(e.into()))?;
                winners_of(&solution, self.__len__())
            }

            /// Solves the game and returns the winners as `solve` and a winning strategy: for
            /// every vertex its successor if it is owned by its winner, else `None`.
            ///
            /// Raises `GameError` if some vertex has no successor.
            fn solve_with_strategy(
                &self,
                py: Python<'_>,
            ) -> PyResult<(Vec<&'static str>, Vec<Option<u32>>)> {
                let solution = py
                    .detach(|| self.0.solve())
                    .map_err(|e: GameError| PyError(e.into()))?;
                let strategy = (0..self.__len__() as u32)
                    .map(|v| {
                        solution
                            .strategy(StateId::from(v))
                            .map(|w| w.into_usize() as u32)
                    })
                    .collect();
                Ok((winners_of(&solution, self.__len__())?, strategy))
            }

            fn __len__(&self) -> usize {
                self.0.arena().state_count()
            }

            fn __repr__(&self) -> String {
                format!("{}(<{} vertices>)", $py_name, self.__len__())
            }
        }
    };
}

parity_game_class!(
    PyMaxEvenParityGame,
    "MaxEvenParityGame",
    MaxEvenParityGame,
    "A parity game in which Eve wins a play if the greatest priority seen infinitely often is even.\n\n\
     >>> game = MaxEvenParityGame([(\"adam\", 1), (\"eve\", 2)], [(0, 0), (0, 1), (1, 0)])\n\
     >>> game.solve()\n\
     ['adam', 'adam']\n\
     >>> game = MaxEvenParityGame([(\"eve\", 1), (\"eve\", 2)], [(0, 0), (0, 1), (1, 0)])\n\
     >>> game.solve()\n\
     ['eve', 'eve']"
);
parity_game_class!(
    PyMinEvenParityGame,
    "MinEvenParityGame",
    MinEvenParityGame,
    "A parity game in which Eve wins a play if the least priority seen infinitely often is even."
);
parity_game_class!(
    PyMaxOddParityGame,
    "MaxOddParityGame",
    MaxOddParityGame,
    "A parity game in which Eve wins a play if the greatest priority seen infinitely often is odd."
);
parity_game_class!(
    PyMinOddParityGame,
    "MinOddParityGame",
    MinOddParityGame,
    "A parity game in which Eve wins a play if the least priority seen infinitely often is odd."
);
