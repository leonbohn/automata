//! Two-player games on finite graphs.
//!
//! Currently, this only contains solvers for parity games ([`ParityGame::solve`] with tangle
//! learning, [`ParityGame::solve_zielonka`] as reference), which also return strategies. A [`ParityGame`] is a thin wrapper
//! around a [`TransitionSystem`] whose state colors are [`Vertex`]es (owner and priority) and whose
//! edges are the moves of the players. The alphabet carries no information, so the default arena
//! [`Arena`] uses a single letter and all edges are labeled with it. All four parity conditions
//! (min/max, even/odd) are supported, see [`ParityCondition`]. The solver is tested against Oink
//! (`tests/oink.rs`). Games can also be built from automata, see [`ParityGame::letter_game`].
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
    alphabet::{Alphabet, Expression, Fixed},
    automaton::{
        MaxEvenParityCondition, MaxOddParityCondition, MinEvenParityCondition,
        MinOddParityCondition, ParityKind,
    },
    math::{FxIndexMap, FxIndexSet},
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

/// The result of solving a [`ParityGame`]: the winner of every vertex and a positional winning
/// strategy for each player.
#[derive(Debug, Clone)]
pub struct Solution<I> {
    winners: FxIndexMap<I, Player>,
    strategy: FxIndexMap<I, I>,
}

impl<I: IdType> Solution<I> {
    /// Returns the player who wins from `vertex`, or `None` if it is not a vertex of the game.
    pub fn winner(&self, vertex: I) -> Option<Player> {
        self.winners.get(&vertex).copied()
    }

    /// Returns the successor that the winner of `vertex` has to pick when it is their turn there,
    /// or `None` if `vertex` is owned by the loser (or not a vertex of the game). Playing these
    /// moves wins from every vertex of the winning region, whatever the opponent does.
    pub fn strategy(&self, vertex: I) -> Option<I> {
        self.strategy.get(&vertex).copied()
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
    /// Solves the game with tangle learning (van Dijk, 2018) and returns the winner of every
    /// vertex together with winning strategies. Fails with [`GameError::NotTotal`] if some vertex
    /// has no successor.
    pub fn solve(&self) -> Result<Solution<T::StateIndex>, GameError> {
        self.solve_with(Solver::tangle_learning)
    }

    /// Solves the game with Zielonka's recursive algorithm. This is slower than
    /// [`ParityGame::solve`] and serves as a reference.
    pub fn solve_zielonka(&self) -> Result<Solution<T::StateIndex>, GameError> {
        self.solve_with(|solver, strategy| {
            let all = vec![true; solver.owner.len()];
            solver.zielonka(&all, strategy).0
        })
    }

    /// Runs `solver`, which returns the vertices won by Eve and fills in the strategy.
    fn solve_with(
        &self,
        solver: impl FnOnce(&Solver, &mut [usize]) -> Vec<bool>,
    ) -> Result<Solution<T::StateIndex>, GameError> {
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

        let solver_state = Solver::new(owner, normalize(C::KIND, &raw), &edges);
        let mut moves = vec![NONE; ids.len()];
        let eve = solver(&solver_state, &mut moves);
        let player = |v: usize| if eve[v] { Player::Eve } else { Player::Adam };
        // `moves` may hold stale entries for vertices owned by the loser
        let strategy = (0..ids.len())
            .filter(|&v| moves[v] != NONE && solver_state.owner[v] == player(v))
            .map(|v| (ids[v], ids[moves[v]]))
            .collect();
        let winners = ids
            .iter()
            .enumerate()
            .map(|(v, q)| (*q, player(v)))
            .collect();
        Ok(Solution { winners, strategy })
    }
}

impl<C: ParityCondition> ParityGame<Arena, C> {
    /// Builds the *letter game* of a (not necessarily deterministic) parity automaton, given by its
    /// transition system `ts` whose edge colors are the priorities and whose condition is `C`.
    /// The `chooser` picks the letters, the opponent resolves nondeterminism by picking an edge
    /// that matches the letter. [`Player::Eve`] wins a play iff the run is accepting, so for a
    /// deterministic automaton and `chooser == Player::Adam`, Eve wins from (the vertex of) the
    /// initial state iff the language is universal. Returns the game and, for each state of
    /// `ts`, the vertex that represents it. A letter without an edge leaves a vertex without
    /// successor, which [`ParityGame::solve`] reports as [`GameError::NotTotal`].
    pub fn letter_game<T>(
        ts: &T,
        chooser: Player,
    ) -> (Self, FxIndexMap<T::StateIndex, StateIndex<Arena>>)
    where
        T: TransitionSystem<EdgeColor = Int> + States,
    {
        // a priority that never decides the winner, because every edge vertex has one as well
        let neutral = match C::KIND {
            ParityKind::MaxEven | ParityKind::MaxOdd => Int::MIN,
            ParityKind::MinEven | ParityKind::MinOdd => Int::MAX,
        };
        let mut game = Self::new();
        let vertices: FxIndexMap<T::StateIndex, StateIndex<Arena>> = ts
            .states()
            .map(|q| (q, game.add_vertex(chooser, neutral)))
            .collect();
        for (&q, &vertex) in &vertices {
            for symbol in ts.alphabet().universe() {
                let edges: Vec<_> = (ts.edges_from(q).into_iter().flatten())
                    .filter(|e| e.expression().matched_by(symbol))
                    .collect();
                let letter = match edges.as_slice() {
                    // the color can sit on the letter vertex itself
                    [e] => game.add_vertex(chooser.opponent(), *e.color()),
                    _ => game.add_vertex(chooser.opponent(), neutral),
                };
                game.add_edge(vertex, letter);
                if let [e] = edges.as_slice() {
                    game.add_edge(letter, vertices[&e.target()]);
                    continue;
                }
                for e in edges {
                    let edge = game.add_vertex(chooser.opponent(), *e.color());
                    game.add_edge(letter, edge);
                    game.add_edge(edge, vertices[&e.target()]);
                }
            }
        }
        (game, vertices)
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

/// Marks a vertex without a chosen successor in a strategy.
const NONE: usize = usize::MAX;

/// The player who wins plays whose greatest priority seen infinitely often is `priority`.
fn favored(priority: usize) -> Player {
    if priority.is_multiple_of(2) {
        Player::Eve
    } else {
        Player::Adam
    }
}

/// Solvers for a max-even game with densely numbered vertices. A strategy is a slice that holds,
/// for each vertex owned by its winner, the chosen successor (other entries are meaningless).
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
    /// [`Player::Eve`] and [`Player::Adam`], in this order. Winning strategies are written to
    /// `strategy`.
    fn zielonka(&self, arena: &[bool], strategy: &mut [usize]) -> (Vec<bool>, Vec<bool>) {
        let n = self.owner.len();
        let priority = &self.priority;
        let Some(max_priority) = (0..n).filter(|&v| arena[v]).map(|v| priority[v]).max() else {
            return (vec![false; n], vec![false; n]);
        };
        let player = favored(max_priority);
        let target: Vec<bool> = (0..n)
            .map(|v| arena[v] && priority[v] == max_priority)
            .collect();
        let attracted = self.attractor(arena, &target, player, strategy);
        let (sub_eve, sub_adam) = self.zielonka(&difference(arena, &attracted), strategy);
        let sub_opponent = match player {
            Player::Eve => sub_adam,
            Player::Adam => sub_eve,
        };

        let (win_player, win_opponent) = if sub_opponent.iter().all(|&b| !b) {
            // `player` wins everything; the top vertices may move anywhere (the play either
            // returns to them infinitely often or stays in the subgame)
            for v in (0..n).filter(|&v| target[v] && self.owner[v] == player) {
                let mut moves = self.successors.of(v).iter().copied();
                strategy[v] = moves.find(|&w| arena[w]).unwrap_or(NONE);
            }
            (arena.to_vec(), vec![false; n])
        } else {
            let attracted = self.attractor(arena, &sub_opponent, player.opponent(), strategy);
            let (sub_eve, sub_adam) = self.zielonka(&difference(arena, &attracted), strategy);
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
    /// i.e. the set of vertices from which `player` can force a visit to `target`. The moves of
    /// `player` that do so are written to `strategy`.
    fn attractor(
        &self,
        arena: &[bool],
        target: &[bool],
        player: Player,
        strategy: &mut [usize],
    ) -> Vec<bool> {
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
                    strategy[v] = w;
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

    /// The out-edges of `v` in the graph that a region of `player` induces: the moves of the
    /// opponent are all edges, `player` only plays its strategy.
    fn region_edges<'a>(&'a self, v: usize, player: Player, moves: &'a [usize]) -> &'a [usize] {
        if self.owner[v] != player {
            self.successors.of(v)
        } else if moves[v] == NONE {
            &[]
        } else {
            std::slice::from_ref(&moves[v])
        }
    }

    /// Tangle learning (van Dijk, "Attracting Tangles to Solve Parity Games", CAV 2018) in the
    /// variant of Oink: repeatedly build the regions of the game top-down (attractors that also
    /// attract known tangles), learn new tangles from closed regions and, as soon as one is
    /// closed for both players, remove the dominion with its attractor. Returns the vertices won
    /// by Eve and writes the winning strategies to `strategy`.
    fn tangle_learning(&self, strategy: &mut [usize]) -> Vec<bool> {
        let n = self.owner.len();
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_by_key(|&v| std::cmp::Reverse(self.priority[v]));
        let mut active = vec![true; n];
        let mut remaining = n;
        let mut eve = vec![false; n];
        let mut tangles = Tangles::new(n);
        while remaining > 0 {
            match self.search(&active, &order, &mut tangles) {
                Search::Dominion {
                    vertices,
                    player,
                    moves,
                } => {
                    let mut target = vec![false; n];
                    for v in vertices {
                        target[v] = true;
                        strategy[v] = moves[v];
                    }
                    let won = self.attractor(&active, &target, player, strategy);
                    for v in (0..n).filter(|&v| won[v]) {
                        eve[v] = player == Player::Eve;
                        active[v] = false;
                        remaining -= 1;
                    }
                    tangles.retain(&active);
                }
                Search::Learned => {}
                Search::Stuck => {
                    // No progress, which the algorithm rules out. Finish with the reference
                    // solver instead of looping, so that the result stays correct regardless.
                    let (won, _) = self.zielonka(&active, strategy);
                    for v in (0..n).filter(|&v| active[v]) {
                        eve[v] = won[v];
                    }
                    break;
                }
            }
        }
        eve
    }

    /// One pass of tangle learning over the vertices in `active`, which are sorted by `order`
    /// (decreasing priority). The pass partitions the game into regions: a region is the
    /// attractor of the vertices of greatest priority (merged with the next ones of the same
    /// parity). If the opponent cannot leave a region (except into regions found before), each
    /// strongly connected component of the player's strategy and the opponent's moves is a
    /// tangle: the player wins every play that stays in it. One that the opponent cannot leave at
    /// all is a dominion.
    fn search(&self, active: &[bool], order: &[usize], tangles: &mut Tangles) -> Search {
        let n = self.owner.len();
        let free = active.to_vec();
        let mut layers = Layers {
            free_count: free.iter().filter(|&&b| b).count(),
            free,
            in_region: vec![false; n],
            region: Vec::new(),
        };
        // number of successors that are not part of a region (yet)
        let mut escs: Vec<usize> = (0..n)
            .map(|v| self.successors.of(v).iter().filter(|&&w| active[w]).count())
            .collect();
        // number of escapes of each tangle that are not attracted (yet)
        let mut tescs: Vec<usize> = tangles.list.iter().map(|t| t.escapes.len()).collect();
        let mut moves = vec![NONE; n];
        // scratch for the SCCs; every vertex is in at most one region
        let mut index = vec![0; n];
        let mut low = vec![0; n];
        let mut on_stack = vec![false; n];
        let mut marked = vec![false; n];
        let mut counter = 1;
        let mut learned = false;
        let mut next = 0;

        while layers.free_count > 0 {
            while !layers.free[order[next]] {
                next += 1;
            }
            let top = self.priority[order[next]];
            let player = favored(top);
            // the heads: all free vertices down to the first one of the other parity
            while next < n {
                let v = order[next];
                if layers.free[v] {
                    if favored(self.priority[v]) != player {
                        break;
                    }
                    layers.join(v);
                }
                next += 1;
            }
            let heads = layers.region.len();

            // attractor; `region` doubles as the queue
            let mut i = 0;
            while i < layers.region.len() {
                let v = layers.region[i];
                i += 1;
                for &from in self.predecessors.of(v) {
                    if !layers.free[from] {
                        continue;
                    }
                    if self.owner[from] == player {
                        moves[from] = v;
                        layers.join(from);
                    } else {
                        escs[from] -= 1;
                        if escs[from] == 0 {
                            layers.join(from);
                        }
                    }
                }
                for &t in &tangles.by_escape[v] {
                    let tangle = &tangles.list[t];
                    if tangle.player != player || tangle.priority > top {
                        continue;
                    }
                    tescs[t] -= 1;
                    if tescs[t] == 0 {
                        for (&u, &s) in tangle.vertices.iter().zip(&tangle.strategy) {
                            if layers.free[u] {
                                moves[u] = s;
                                layers.join(u);
                            }
                        }
                    }
                }
            }

            // heads of the player need a move that stays in the region, if there is one
            for &h in &layers.region[..heads] {
                if self.owner[h] == player {
                    let mut stay = self.successors.of(h).iter().copied();
                    moves[h] = stay.find(|&w| layers.in_region[w]).unwrap_or(NONE);
                }
            }
            // the region is closed if the opponent cannot leave to the free vertices
            let leaks = layers.free_count > 0
                && layers.region[..heads].iter().any(|&h| {
                    if self.owner[h] == player {
                        moves[h] == NONE
                    } else {
                        self.successors.of(h).iter().any(|&w| layers.free[w])
                    }
                });

            if !leaks {
                let mut components: Vec<Vec<usize>> = Vec::new();
                let mut stack = Vec::new();
                let mut calls: Vec<(usize, usize)> = Vec::new();
                for &root in &layers.region {
                    if index[root] != 0 {
                        continue;
                    }
                    (index[root], low[root]) = (counter, counter);
                    counter += 1;
                    stack.push(root);
                    on_stack[root] = true;
                    calls.push((root, 0));
                    while let Some(&(v, position)) = calls.last() {
                        if let Some(&w) = self.region_edges(v, player, &moves).get(position) {
                            if let Some(call) = calls.last_mut() {
                                call.1 += 1;
                            }
                            if !layers.in_region[w] {
                                continue;
                            }
                            if index[w] == 0 {
                                (index[w], low[w]) = (counter, counter);
                                counter += 1;
                                stack.push(w);
                                on_stack[w] = true;
                                calls.push((w, 0));
                            } else if on_stack[w] {
                                low[v] = low[v].min(index[w]);
                            }
                            continue;
                        }
                        calls.pop();
                        if let Some(&(parent, _)) = calls.last() {
                            low[parent] = low[parent].min(low[v]);
                        }
                        if low[v] == index[v] {
                            let mut component = Vec::new();
                            while let Some(w) = stack.pop() {
                                on_stack[w] = false;
                                component.push(w);
                                if w == v {
                                    break;
                                }
                            }
                            components.push(component);
                        }
                    }
                }

                let mut dominion = Vec::new();
                for mut component in components {
                    let cyclic = component.len() > 1
                        || self
                            .region_edges(component[0], player, &moves)
                            .contains(&component[0]);
                    if !cyclic {
                        continue;
                    }
                    component.sort_unstable();
                    // the escapes: where the opponent can leave the component
                    for &v in &component {
                        marked[v] = true;
                    }
                    let mut escapes = Vec::new();
                    for &v in component.iter().filter(|&&v| self.owner[v] != player) {
                        for &w in self.successors.of(v) {
                            if active[w] && !marked[w] {
                                marked[w] = true;
                                escapes.push(w);
                            }
                        }
                    }
                    for &v in component.iter().chain(&escapes) {
                        marked[v] = false;
                    }
                    if escapes.is_empty() {
                        dominion.extend(component);
                    } else if !tangles.known.contains(&component) {
                        tescs.push(escapes.len());
                        tangles.add(Tangle {
                            player,
                            priority: component
                                .iter()
                                .map(|&v| self.priority[v])
                                .max()
                                .unwrap_or(0),
                            strategy: (component.iter())
                                .map(|&v| {
                                    if self.owner[v] == player {
                                        moves[v]
                                    } else {
                                        NONE
                                    }
                                })
                                .collect(),
                            vertices: component,
                            escapes,
                        });
                        learned = true;
                    }
                }
                if !dominion.is_empty() {
                    return Search::Dominion {
                        vertices: dominion,
                        player,
                        moves,
                    };
                }
            }
            for v in layers.region.drain(..) {
                layers.in_region[v] = false;
            }
        }
        if learned {
            Search::Learned
        } else {
            Search::Stuck
        }
    }
}

/// The result of a pass of [`Solver::search`].
enum Search {
    /// A set that `player` wins by playing `moves` and that the opponent cannot leave.
    Dominion {
        vertices: Vec<usize>,
        player: Player,
        moves: Vec<usize>,
    },
    /// Some new tangle was found.
    Learned,
    /// Neither of the above.
    Stuck,
}

/// The vertices of a pass of [`Solver::search`] that are not part of a region yet, and the
/// vertices of the current region.
struct Layers {
    free: Vec<bool>,
    free_count: usize,
    in_region: Vec<bool>,
    region: Vec<usize>,
}

impl Layers {
    /// Adds the free vertex `v` to the current region.
    fn join(&mut self, v: usize) {
        self.free[v] = false;
        self.free_count -= 1;
        self.in_region[v] = true;
        self.region.push(v);
    }
}

/// A tangle: a set of vertices that `player` wins every play in that stays inside, when
/// playing `strategy` (only meaningful for the vertices of `player`). The opponent can leave
/// the tangle only to the `escapes`. `vertices` is sorted.
struct Tangle {
    player: Player,
    /// The greatest priority in the tangle.
    priority: usize,
    vertices: Vec<usize>,
    strategy: Vec<usize>,
    escapes: Vec<usize>,
}

/// The tangles found so far, without duplicates.
struct Tangles {
    list: Vec<Tangle>,
    known: FxIndexSet<Vec<usize>>,
    /// For each vertex the tangles that have it as an escape.
    by_escape: Vec<Vec<usize>>,
}

impl Tangles {
    fn new(vertices: usize) -> Self {
        Self {
            list: Vec::new(),
            known: FxIndexSet::default(),
            by_escape: vec![Vec::new(); vertices],
        }
    }

    fn add(&mut self, tangle: Tangle) {
        for &e in &tangle.escapes {
            self.by_escape[e].push(self.list.len());
        }
        self.known.insert(tangle.vertices.clone());
        self.list.push(tangle);
    }

    /// Forgets the tangles that are not completely in the game `active` any more (including
    /// their escapes, which would otherwise be stale).
    fn retain(&mut self, active: &[bool]) {
        let old = std::mem::take(&mut self.list);
        self.known.clear();
        self.by_escape.iter_mut().for_each(Vec::clear);
        for tangle in old {
            if tangle
                .vertices
                .iter()
                .chain(&tangle.escapes)
                .all(|&v| active[v])
            {
                self.add(tangle);
            }
        }
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

    /// Checks that `solution` is consistent: the strategy of the winner of each vertex stays in
    /// its winning region and no play consistent with it has a bad greatest priority.
    fn check_strategies(game: &MaxEvenParityGame, solution: &Solution<StateIndex<Arena>>) {
        let ts = game.arena();
        let n = ts.state_count();
        let id = |i| StateIndex::<Arena>::from_dense(i).unwrap();
        let winner = |i| solution.winner(id(i)).unwrap();
        // the edges that remain when the winner of the target sticks to the strategy
        let edges = |v: usize| -> Vec<usize> {
            let vertex = ts.state_color(id(v)).unwrap();
            if vertex.owner == winner(v) {
                let w = solution.strategy(id(v)).expect("winner has a move");
                vec![w.to_dense().unwrap()]
            } else {
                (ts.edges_from(id(v))
                    .unwrap()
                    .map(|e| e.target().to_dense().unwrap()))
                .collect()
            }
        };
        for v in 0..n {
            let vertex = ts.state_color(id(v)).unwrap();
            assert!(edges(v).iter().all(|&w| winner(w) == winner(v)));
            assert_eq!(
                solution.strategy(id(v)).is_some(),
                vertex.owner == winner(v)
            );
            // a cycle through `v` in which `v` has the greatest priority is bad if the
            // parity of `v` is the one of the loser
            if favored(usize::from(vertex.priority)) == winner(v) {
                continue;
            }
            let mut seen = vec![false; n];
            let mut todo = edges(v);
            while let Some(w) = todo.pop() {
                let p = ts.state_color(id(w)).unwrap().priority;
                if seen[w] || p > vertex.priority {
                    continue;
                }
                seen[w] = true;
                todo.extend(edges(w));
            }
            assert!(!seen[v], "winner of {v} is bad");
        }
    }

    use proptest::strategy::Strategy as _;

    proptest::proptest! {
        #[test]
        fn solvers_agree(
            game in (1usize..12).prop_flat_map(|n| {
                proptest::collection::vec(
                    (proptest::bool::ANY, 0u8..6, proptest::collection::vec(0..n, 1..4)),
                    n,
                )
            })
        ) {
            let mut g = MaxEvenParityGame::new();
            let ids: Vec<_> = game
                .iter()
                .map(|(adam, p, _)| g.add_vertex(if *adam { Player::Adam } else { Player::Eve }, *p))
                .collect();
            for (v, (_, _, successors)) in game.iter().enumerate() {
                for &w in successors {
                    g.add_edge(ids[v], ids[w]);
                }
            }
            let fast = g.solve().unwrap();
            let reference = g.solve_zielonka().unwrap();
            for &v in &ids {
                proptest::prop_assert_eq!(fast.winner(v), reference.winner(v));
            }
            check_strategies(&g, &fast);
            check_strategies(&g, &reference);
        }
    }

    #[test]
    fn letter_game_decides_universality() {
        use crate::ts::{Builder, Pointed};
        // the smallest priority seen infinitely often is always even
        let universal = Builder::without_state_colors()
            .with_transitions([(0, 'a', 0, 0), (0, 'b', 2, 0)])
            .into_dpa(0);
        // `b^ω` is rejected
        let other = Builder::without_state_colors()
            .with_transitions([(0, 'a', 0, 0), (0, 'b', 1, 0)])
            .into_dpa(0);
        for (dpa, expected) in [(universal, Player::Eve), (other, Player::Adam)] {
            let (game, vertices) = MinEvenParityGame::letter_game(dpa.ts(), Player::Adam);
            let solution = game.solve().unwrap();
            assert_eq!(solution.winner(vertices[&dpa.initial()]), Some(expected));
        }
    }
}
