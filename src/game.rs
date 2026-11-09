//! Two-player games on finite graphs.
//!
//! Currently, this only contains a solver for parity games. A [`ParityGame`] is a thin wrapper
//! around a [`TransitionSystem`] whose state colors are [`Vertex`]es (owner and priority) and whose
//! edges are the moves of the players. The alphabet carries no information, so the default arena
//! [`Arena`] uses a single letter and all edges are labeled with it. All four parity conditions
//! (min/max, even/odd) are supported, see [`ParityCondition`]. The solver is tested against Oink
//! (`tests/oink.rs`).
//!
//! ```
//! use automata::game::{MaxEvenParityGame, Player};
//!
//! let mut game = MaxEvenParityGame::new();
//! let v0 = game.add_vertex(Player::Adam, 1);
//! let v1 = game.add_vertex(Player::Eve, 2);
//! game.add_edge(v0, v0);
//! game.add_edge(v0, v1);
//! game.add_edge(v1, v0);
//! // Adam stays in `v0` forever and sees only priority 1
//! let solution = game.solve().unwrap();
//! assert_eq!(solution.winner(v0), Some(Player::Adam));
//! ```

use std::marker::PhantomData;

use crate::{
    Int, TransitionSystem, Void,
    alphabet::Fixed,
    automaton::{
        MaxEvenParityCondition, MaxOddParityCondition, MinEvenParityCondition,
        MinOddParityCondition, ParityKind,
    },
    math::FxIndexMap,
    ts::{IdType, LinkedTs, Sproutable, StateIndex, States},
};

/// One of the two players of a [`ParityGame`]. The meaning of "winning" depends on the
/// [`ParityCondition`] of the game: for [`MaxEvenParityCondition`], [`Player::Eve`] wins a play iff
/// the greatest priority that occurs infinitely often is even.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Player {
    /// Existential player.
    Eve,
    /// Universal player.
    Adam,
}

impl Player {
    /// Returns the other player.
    pub fn opponent(self) -> Self {
        match self {
            Player::Eve => Player::Adam,
            Player::Adam => Player::Eve,
        }
    }
}

/// The color of a vertex of a [`ParityGame`]: the player who moves from it and its priority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Vertex {
    /// The player who chooses the successor.
    pub owner: Player,
    /// The priority that is seen when the play visits the vertex.
    pub priority: Int,
}

/// Errors that can occur when solving a game.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum GameError {
    /// Some vertex has no successor, but the arena of a parity game must be total.
    #[error("the arena of a parity game must be total, but some vertex has no successor")]
    NotTotal,
    /// A game in the PGSolver format could not be read.
    #[error(transparent)]
    PgSolver(#[from] PgSolverError),
}

/// A game in the PGSolver format could not be read, see [`ParityGame::from_pgsolver`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
#[error("invalid PGSolver game in statement {statement}: {reason}")]
pub struct PgSolverError {
    /// The number of the offending statement (terminated by `;`), counted from one.
    pub statement: usize,
    /// What is wrong with it.
    pub reason: &'static str,
}

mod sealed {
    pub trait Sealed {}
}

/// Marker for the four parity conditions that [`ParityGame`]s can be played with.
pub trait ParityCondition: sealed::Sealed {
    /// The kind of parity condition.
    const KIND: ParityKind;
}

macro_rules! parity_condition {
    ($cond:ident, $kind:ident) => {
        impl sealed::Sealed for $cond {}
        impl ParityCondition for $cond {
            const KIND: ParityKind = ParityKind::$kind;
        }
    };
}
parity_condition!(MaxEvenParityCondition, MaxEven);
parity_condition!(MinEvenParityCondition, MinEven);
parity_condition!(MaxOddParityCondition, MaxOdd);
parity_condition!(MinOddParityCondition, MinOdd);

/// The default storage of a game: all edges carry the same letter, nondeterminism is the choice
/// of the owner of the source vertex.
pub type Arena = LinkedTs<Fixed<char, 1>, Vertex, Void>;

/// A parity game on the arena `T`, which is any [`TransitionSystem`] with [`Vertex`] state colors.
/// The arena must be *total*, i.e. every vertex needs at least one successor, which
/// [`ParityGame::solve`] checks.
#[derive(Debug, Clone)]
pub struct ParityGame<T = Arena, C = MaxEvenParityCondition> {
    ts: T,
    condition: PhantomData<C>,
}

/// A parity game in which the greatest priority seen infinitely often has to be even for Eve.
pub type MaxEvenParityGame<T = Arena> = ParityGame<T, MaxEvenParityCondition>;
/// A parity game in which the least priority seen infinitely often has to be even for Eve.
pub type MinEvenParityGame<T = Arena> = ParityGame<T, MinEvenParityCondition>;
/// A parity game in which the greatest priority seen infinitely often has to be odd for Eve.
pub type MaxOddParityGame<T = Arena> = ParityGame<T, MaxOddParityCondition>;
/// A parity game in which the least priority seen infinitely often has to be odd for Eve.
pub type MinOddParityGame<T = Arena> = ParityGame<T, MinOddParityCondition>;

impl<T, C> ParityGame<T, C> {
    /// Wraps an existing arena.
    pub fn from_arena(ts: T) -> Self {
        Self {
            ts,
            condition: PhantomData,
        }
    }

    /// Returns the underlying arena.
    pub fn arena(&self) -> &T {
        &self.ts
    }
}

impl<C> ParityGame<Arena, C> {
    /// Creates a game without vertices.
    pub fn new() -> Self {
        Self::from_arena(LinkedTs::with_capacity(Fixed::from(['x']), 0))
    }

    /// Adds a vertex owned by `owner` with the given `priority` and returns its index.
    pub fn add_vertex(&mut self, owner: Player, priority: Int) -> StateIndex<Arena> {
        self.ts.add_state(Vertex { owner, priority })
    }

    /// Adds an edge from `source` to `target`.
    pub fn add_edge(&mut self, source: StateIndex<Arena>, target: StateIndex<Arena>) {
        self.ts.add_edge((source, 'x', Void, target));
    }
}

impl<C> ParityGame<Arena, C> {
    /// Reads a game in the [PGSolver format](https://github.com/tcsprojects/pgsolver): an optional
    /// header `parity n;` followed by one statement `id priority owner successors "name";` per
    /// vertex, where `successors` is a comma separated list, `owner` is `0` for [`Player::Eve`]
    /// and `1` for [`Player::Adam`] and the name is optional and ignored. The ids must be exactly
    /// `0..n` (in any order) and the vertices of the game are numbered like them.
    ///
    /// The format does not say who wins a play, PGSolver and Oink use max-even priorities. The
    /// condition `C` of the game gives the priorities their meaning.
    ///
    /// ```
    /// use automata::game::{MaxEvenParityGame, Player};
    ///
    /// let game = MaxEvenParityGame::from_pgsolver("parity 1;\n0 1 1 0,1;\n1 2 0 0;\n")?;
    /// assert_eq!(game.to_pgsolver(), "parity 1;\n0 1 1 0,1;\n1 2 0 0;\n");
    /// # Ok::<(), automata::game::GameError>(())
    /// ```
    pub fn from_pgsolver(input: &str) -> Result<Self, GameError> {
        fn err(statement: usize, reason: &'static str) -> GameError {
            PgSolverError { statement, reason }.into()
        }
        let mut statements = input
            .split(';')
            .map(str::trim)
            .enumerate()
            .map(|(i, s)| (i + 1, s))
            .filter(|(_, s)| !s.is_empty())
            .peekable();
        let mut declared = None; // (statement, n)
        if let Some(&(i, header)) = statements.peek()
            && let Some(rest) = header.strip_prefix("parity")
        {
            let max: usize = rest
                .trim()
                .parse()
                .map_err(|_| err(i, "the header must be `parity n`"))?;
            declared = Some((i, max));
            statements.next();
        }

        // every id must occur exactly once, so there are as many statements as vertices
        let statements: Vec<_> = statements.collect();
        let n = statements.len();
        if let Some((i, max)) = declared
            && max.checked_add(1) != Some(n)
        {
            return Err(err(i, "the header does not match the number of vertices"));
        }
        let mut vertices: Vec<Option<(Vertex, Vec<usize>)>> = vec![None; n];
        for (i, statement) in statements {
            // the name is the part in quotes, everything before it are the fields
            let fields = statement.split('"').next().unwrap_or_default();
            let mut fields = fields.split_whitespace();
            let mut next = |reason| fields.next().ok_or_else(|| err(i, reason));
            let id: usize = next("missing id")?
                .parse()
                .map_err(|_| err(i, "the id is not a number"))?;
            let priority: Int = next("missing priority")?
                .parse()
                .map_err(|_| err(i, "the priority is not a number from 0 to 255"))?;
            let owner = match next("missing owner")? {
                "0" => Player::Eve,
                "1" => Player::Adam,
                _ => return Err(err(i, "the owner must be 0 or 1")),
            };
            let successors = fields.collect::<String>();
            let successors: Vec<usize> = successors
                .split(',')
                .map(|w| match w.parse() {
                    Ok(w) if w < n => Ok(w),
                    _ => Err(err(i, "a successor is not the id of a vertex")),
                })
                .collect::<Result<_, _>>()?;
            let slot = vertices
                .get_mut(id)
                .ok_or_else(|| err(i, "the ids must be exactly 0..n"))?;
            if slot
                .replace((Vertex { owner, priority }, successors))
                .is_some()
            {
                return Err(err(i, "the id occurs twice"));
            }
        }

        let mut game = Self::new();
        let ids: Vec<_> = vertices
            .iter()
            .flatten()
            .map(|(v, _)| game.add_vertex(v.owner, v.priority))
            .collect();
        for (v, (_, successors)) in vertices.iter().flatten().enumerate() {
            for &w in successors {
                game.add_edge(ids[v], ids[w]);
            }
        }
        Ok(game)
    }
}

impl<T, C> ParityGame<T, C>
where
    T: TransitionSystem<StateColor = Vertex> + States,
{
    /// Writes the game in the PGSolver format, see [`ParityGame::from_pgsolver`]. The vertices are
    /// numbered in the order of [`States::states`] and the successors are sorted. A vertex without a successor is written with
    /// an empty list of successors, which no solver accepts.
    pub fn to_pgsolver(&self) -> String {
        use std::fmt::Write;
        let ids: Vec<T::StateIndex> = self.ts.states().collect();
        let index: FxIndexMap<T::StateIndex, usize> =
            ids.iter().enumerate().map(|(i, q)| (*q, i)).collect();
        let mut out = format!("parity {};\n", ids.len().saturating_sub(1));
        for (v, q) in ids.iter().enumerate() {
            let Some(vertex) = self.ts.state_color(*q) else {
                continue;
            };
            let owner = u8::from(vertex.owner == Player::Adam);
            // sorted, so that the output does not depend on the order of the storage
            let mut successors: Vec<usize> = (self.ts.edges_from(*q).into_iter().flatten())
                .map(|e| index[&e.target()])
                .collect();
            successors.sort_unstable();
            let successors: Vec<_> = successors.iter().map(usize::to_string).collect();
            let _ = writeln!(
                out,
                "{v} {} {owner} {};",
                vertex.priority,
                successors.join(",")
            );
        }
        out
    }
}

impl<C> Default for ParityGame<Arena, C> {
    fn default() -> Self {
        Self::new()
    }
}

/// The result of solving a [`ParityGame`]: the winner of every vertex.
#[derive(Debug, Clone)]
pub struct Solution<I> {
    winners: FxIndexMap<I, Player>,
}

impl<I: IdType> Solution<I> {
    /// Returns the player who wins from `vertex`, or `None` if it is not a vertex of the game.
    pub fn winner(&self, vertex: I) -> Option<Player> {
        self.winners.get(&vertex).copied()
    }

    /// Returns the vertices from which `player` wins.
    pub fn winning_region(&self, player: Player) -> impl Iterator<Item = I> + '_ {
        self.winners
            .iter()
            .filter(move |(_, p)| **p == player)
            .map(|(v, _)| *v)
    }
}

impl<T, C> ParityGame<T, C>
where
    T: TransitionSystem<StateColor = Vertex> + States,
    C: ParityCondition,
{
    /// Solves the game using Zielonka's recursive algorithm and returns the winner of every
    /// vertex. Fails with [`GameError::NotTotal`] if some vertex has no successor.
    pub fn solve(&self) -> Result<Solution<T::StateIndex>, GameError> {
        let ids: Vec<T::StateIndex> = self.ts.states().collect();
        let index: FxIndexMap<T::StateIndex, usize> =
            ids.iter().enumerate().map(|(i, q)| (*q, i)).collect();

        let mut owner = Vec::with_capacity(ids.len());
        let mut raw = Vec::with_capacity(ids.len());
        let mut edges = Vec::new();
        for (v, q) in ids.iter().enumerate() {
            let vertex = self.ts.state_color(*q).ok_or(GameError::NotTotal)?;
            owner.push(vertex.owner);
            raw.push(usize::from(vertex.priority));
            let mut any = false;
            for edge in self.ts.edges_from(*q).into_iter().flatten() {
                any = true;
                edges.push((v, index[&edge.target()]));
            }
            if !any {
                return Err(GameError::NotTotal);
            }
        }

        let solver = Solver::new(owner, normalize(C::KIND, &raw), &edges);
        let all = vec![true; ids.len()];
        let (eve, _) = solver.zielonka(&all);
        let winners = ids
            .into_iter()
            .zip(eve)
            .map(|(q, eve)| (q, if eve { Player::Eve } else { Player::Adam }))
            .collect();
        Ok(Solution { winners })
    }
}

/// Turns the priorities of a game of the given kind into priorities of a max-even game with
/// the same winners. Min is turned into max by `p -> m - p`, odd into even by adding one. `m` is
/// even, so that the parity of `m - p` is the one of `p`.
fn normalize(kind: ParityKind, priorities: &[usize]) -> Vec<usize> {
    let m = priorities
        .iter()
        .copied()
        .max()
        .unwrap_or(0)
        .next_multiple_of(2);
    priorities
        .iter()
        .map(|&p| match kind {
            ParityKind::MaxEven => p,
            ParityKind::MaxOdd => p + 1,
            ParityKind::MinEven => m - p,
            ParityKind::MinOdd => m - p + 1,
        })
        .collect()
}

/// The adjacency lists of all vertices of a game, stored contiguously: the neighbors of `v` are
/// `neighbors[start[v]..start[v + 1]]`.
struct Adjacency {
    start: Vec<usize>,
    neighbors: Vec<usize>,
}

impl Adjacency {
    /// Builds the adjacency lists of the vertices `0..size` from the given `(vertex, neighbor)`
    /// pairs.
    fn new(size: usize, pairs: impl Iterator<Item = (usize, usize)> + Clone) -> Self {
        // first count the neighbors of each vertex, then let each list start where the
        // previous one ends
        let mut start = vec![0; size + 1];
        for (v, _) in pairs.clone() {
            start[v + 1] += 1;
        }
        for v in 0..size {
            start[v + 1] += start[v];
        }
        let mut next = start.clone();
        let mut neighbors = vec![0; start[size]];
        for (v, w) in pairs {
            neighbors[next[v]] = w;
            next[v] += 1;
        }
        Self { start, neighbors }
    }

    /// Returns the neighbors of `v`.
    fn of(&self, v: usize) -> &[usize] {
        &self.neighbors[self.start[v]..self.start[v + 1]]
    }
}

/// Zielonka's algorithm on a max-even game with densely numbered vertices.
struct Solver {
    owner: Vec<Player>,
    priority: Vec<usize>,
    successors: Adjacency,
    predecessors: Adjacency,
}

impl Solver {
    fn new(owner: Vec<Player>, priority: Vec<usize>, edges: &[(usize, usize)]) -> Self {
        let n = owner.len();
        let edges = edges.iter().copied();
        Self {
            owner,
            priority,
            successors: Adjacency::new(n, edges.clone()),
            predecessors: Adjacency::new(n, edges.map(|(v, w)| (w, v))),
        }
    }

    /// Solves the subgame induced by the vertices in `arena` (which must be a trap for both
    /// players, so that the subgame is again total) and returns the winning regions of
    /// [`Player::Eve`] and [`Player::Adam`], in this order.
    fn zielonka(&self, arena: &[bool]) -> (Vec<bool>, Vec<bool>) {
        let n = self.owner.len();
        let priority = &self.priority;
        let Some(max_priority) = (0..n).filter(|&v| arena[v]).map(|v| priority[v]).max() else {
            return (vec![false; n], vec![false; n]);
        };
        let player = if max_priority.is_multiple_of(2) {
            Player::Eve
        } else {
            Player::Adam
        };
        let target: Vec<bool> = (0..n)
            .map(|v| arena[v] && priority[v] == max_priority)
            .collect();
        let attracted = self.attractor(arena, &target, player);
        let (sub_eve, sub_adam) = self.zielonka(&difference(arena, &attracted));
        let sub_opponent = match player {
            Player::Eve => sub_adam,
            Player::Adam => sub_eve,
        };

        let (win_player, win_opponent) = if sub_opponent.iter().all(|&b| !b) {
            (arena.to_vec(), vec![false; n])
        } else {
            let attracted = self.attractor(arena, &sub_opponent, player.opponent());
            let (sub_eve, sub_adam) = self.zielonka(&difference(arena, &attracted));
            let (sub_player, sub_opponent) = match player {
                Player::Eve => (sub_eve, sub_adam),
                Player::Adam => (sub_adam, sub_eve),
            };
            (sub_player, union(&sub_opponent, &attracted))
        };

        match player {
            Player::Eve => (win_player, win_opponent),
            Player::Adam => (win_opponent, win_player),
        }
    }

    /// Computes the attractor of `target` for `player` within the subgame induced by `arena`,
    /// i.e. the set of vertices from which `player` can force a visit to `target`.
    fn attractor(&self, arena: &[bool], target: &[bool], player: Player) -> Vec<bool> {
        let n = self.owner.len();
        let mut attracted = target.to_vec();
        // for vertices of the opponent: number of successors (within `arena`) that are not yet
        // attracted; such a vertex is attracted once this drops to zero
        let mut remaining: Vec<usize> = (0..n)
            .map(|v| self.successors.of(v).iter().filter(|&&w| arena[w]).count())
            .collect();
        let mut queue: Vec<usize> = (0..n).filter(|&v| attracted[v]).collect();
        while let Some(w) = queue.pop() {
            for &v in self.predecessors.of(w) {
                if !arena[v] || attracted[v] {
                    continue;
                }
                if self.owner[v] == player {
                    attracted[v] = true;
                    queue.push(v);
                } else {
                    remaining[v] -= 1;
                    if remaining[v] == 0 {
                        attracted[v] = true;
                        queue.push(v);
                    }
                }
            }
        }
        attracted
    }
}

// for each pair of a and b: returns true only on a = true and b = false
fn difference(a: &[bool], b: &[bool]) -> Vec<bool> {
    a.iter().zip(b).map(|(&x, &y)| x && !y).collect()
}

fn union(a: &[bool], b: &[bool]) -> Vec<bool> {
    a.iter().zip(b).map(|(&x, &y)| x || y).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Solves `game` and returns the winners in order of creation of the vertices.
    fn winners<C: ParityCondition>(game: &ParityGame<Arena, C>, n: usize) -> Vec<Player> {
        let solution = game.solve().unwrap();
        (0..n)
            .map(|i| {
                solution
                    .winner(StateIndex::<Arena>::from_dense(i).unwrap())
                    .unwrap()
            })
            .collect()
    }

    #[test]
    fn single_self_loops() {
        let mut game = MaxEvenParityGame::new();
        let even = game.add_vertex(Player::Adam, 2);
        let odd = game.add_vertex(Player::Eve, 1);
        game.add_edge(even, even);
        game.add_edge(odd, odd);
        assert_eq!(winners(&game, 2), vec![Player::Eve, Player::Adam]);
    }

    #[test]
    fn choices_matter() {
        // v0 (Eve, 0) can move to v1 (priority 1, self-loop) or v2 (priority 2, self-loop).
        // v3 (Adam, 0) can move to v1 or v2 as well.
        let mut game = MaxEvenParityGame::new();
        let v0 = game.add_vertex(Player::Eve, 0);
        let v1 = game.add_vertex(Player::Eve, 1);
        let v2 = game.add_vertex(Player::Eve, 2);
        let v3 = game.add_vertex(Player::Adam, 0);
        for v in [v0, v3] {
            game.add_edge(v, v1);
            game.add_edge(v, v2);
        }
        game.add_edge(v1, v1);
        game.add_edge(v2, v2);
        assert_eq!(
            winners(&game, 4),
            vec![Player::Eve, Player::Adam, Player::Eve, Player::Adam]
        );
    }

    #[test]
    fn cycle_through_high_priority() {
        // Adam owns v0 and can either stay in v0 (priority 1) forever or move to v1, which
        // has priority 2 and leads back to v0. Staying is winning for Adam.
        let mut game = MaxEvenParityGame::new();
        let v0 = game.add_vertex(Player::Adam, 1);
        let v1 = game.add_vertex(Player::Eve, 2);
        game.add_edge(v0, v0);
        game.add_edge(v0, v1);
        game.add_edge(v1, v0);
        assert_eq!(winners(&game, 2), vec![Player::Adam, Player::Adam]);

        // if Eve owns v0, she moves to v1 and sees priority 2 infinitely often
        let mut game = MaxEvenParityGame::new();
        let v0 = game.add_vertex(Player::Eve, 1);
        let v1 = game.add_vertex(Player::Eve, 2);
        game.add_edge(v0, v0);
        game.add_edge(v0, v1);
        game.add_edge(v1, v0);
        assert_eq!(winners(&game, 2), vec![Player::Eve, Player::Eve]);
    }

    /// The example from the lecture "Infinite Computation and Games" by Christof Löding (RWTH),
    /// with the given priorities (indexed by vertex).
    fn icag<C: ParityCondition>(priorities: [Int; 8]) -> ParityGame<Arena, C> {
        use Player::{Adam, Eve};
        let mut game = ParityGame::new();
        let owners = [Eve, Adam, Adam, Adam, Adam, Eve, Adam, Eve];
        let v: Vec<_> = owners
            .iter()
            .zip(priorities)
            .map(|(&o, p)| game.add_vertex(o, p))
            .collect();
        for (a, b) in [
            (0, 1),
            (0, 4),
            (1, 0),
            (1, 2),
            (1, 5),
            (2, 3),
            (2, 5),
            (3, 7),
            (4, 0),
            (4, 5),
            (5, 1),
            (5, 2),
            (6, 2),
            (6, 7),
            (7, 6),
            (7, 3),
        ] {
            game.add_edge(v[a], v[b]);
        }
        game
    }

    #[test]
    fn icag_example() {
        use Player::{Adam, Eve};
        let expected = vec![Adam, Adam, Eve, Eve, Adam, Eve, Eve, Eve];
        let game = icag::<MaxEvenParityCondition>([3, 2, 2, 3, 2, 0, 4, 1]);
        assert_eq!(winners(&game, 8), expected);
    }

    #[test]
    fn all_conditions_agree() {
        // Max-even priorities p, rewritten for the other three conditions so that Eve wins
        // exactly the same plays: min-even uses 6 - p, odd conditions shift by one.
        let p = [3u8, 2, 2, 3, 2, 0, 4, 1];
        let expected = winners(&icag::<MaxEvenParityCondition>(p), 8);
        assert_eq!(
            winners(&icag::<MaxOddParityCondition>(p.map(|x| x + 1)), 8),
            expected
        );
        assert_eq!(
            winners(&icag::<MinEvenParityCondition>(p.map(|x| 6 - x)), 8),
            expected
        );
        assert_eq!(
            winners(&icag::<MinOddParityCondition>(p.map(|x| 7 - x)), 8),
            expected
        );
    }

    #[test]
    fn pgsolver_roundtrip() {
        let game = icag::<MaxEvenParityCondition>([3, 2, 2, 3, 2, 0, 4, 1]);
        let text = game.to_pgsolver();
        assert!(text.starts_with("parity 7;\n0 3 0 1,4;\n"));
        let read = MaxEvenParityGame::from_pgsolver(&text).unwrap();
        assert_eq!(read.to_pgsolver(), text);
        assert_eq!(winners(&read, 8), winners(&game, 8));
    }

    #[test]
    fn pgsolver_reads_names_whitespace_and_any_order() {
        let text = "parity 1;\n1 0 1 0, 1 \"b\";\n  0 3 0 1;\n";
        let game = MaxEvenParityGame::from_pgsolver(text).unwrap();
        assert_eq!(game.to_pgsolver(), "parity 1;\n0 3 0 1;\n1 0 1 0,1;\n");
        // the header is optional
        let game = MaxEvenParityGame::from_pgsolver("0 1 0 0;").unwrap();
        assert_eq!(game.to_pgsolver(), "parity 0;\n0 1 0 0;\n");
    }

    #[test]
    fn pgsolver_rejects_invalid_input() {
        for text in [
            "parity x;",           // header
            "parity 2;\n0 0 0 0;", // header does not match
            "0 0 0 0;\n0 0 0 0;",  // id twice
            "0 0 0 0;\n2 0 0 0;",  // id out of range
            "0 0 2 0;",            // owner
            "0 256 0 0;",          // priority
            "0 0 0 1;",            // successor
            "0 0 0;",              // no successors
            "0 0",                 // too short
            "a 0 0 0;",            // id
        ] {
            assert!(
                matches!(
                    MaxEvenParityGame::from_pgsolver(text),
                    Err(GameError::PgSolver(_))
                ),
                "{text:?}"
            );
        }
    }

    #[test]
    fn not_total() {
        let mut game = MaxEvenParityGame::new();
        let v = game.add_vertex(Player::Eve, 0);
        let w = game.add_vertex(Player::Eve, 0);
        game.add_edge(v, w);
        assert_eq!(game.solve().unwrap_err(), GameError::NotTotal);
    }
}
