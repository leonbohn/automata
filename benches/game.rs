//! Solving parity games with Zielonka's algorithm.

use automata::game::{Arena, MaxEvenParityGame, MinOddParityGame, Player};
use gungraun::{Dhat, prelude::*};
use std::hint::black_box;

/// A xorshift generator, so that the games are the same on every machine.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

/// Random game with `n` vertices, `1..=3` successors each and priorities `0..priorities`.
fn random(n: usize, priorities: usize) -> (usize, MaxEvenParityGame) {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    let mut game = MaxEvenParityGame::new();
    let ids: Vec<_> = (0..n)
        .map(|_| {
            let owner = if rng.below(2) == 0 {
                Player::Eve
            } else {
                Player::Adam
            };
            game.add_vertex(owner, rng.below(priorities) as u8)
        })
        .collect();
    for &v in &ids {
        for _ in 0..1 + rng.below(3) {
            game.add_edge(v, ids[rng.below(n)]);
        }
    }
    (n, game)
}

fn random_few(n: usize) -> (usize, MaxEvenParityGame) {
    random(n, 4)
}
fn random_many(n: usize) -> (usize, MaxEvenParityGame) {
    random(n, 64)
}

/// A ring whose vertices alternate between the players and have cycling priorities, with an edge
/// from every vertex back to the first.
fn ladder(n: usize) -> (usize, MaxEvenParityGame) {
    let mut game = MaxEvenParityGame::new();
    let ids: Vec<_> = (0..n)
        .map(|i| {
            let owner = if i % 2 == 0 {
                Player::Eve
            } else {
                Player::Adam
            };
            game.add_vertex(owner, (i % 32) as u8)
        })
        .collect();
    for i in 0..n {
        game.add_edge(ids[i], ids[(i + 1) % n]);
        game.add_edge(ids[i], ids[0]);
    }
    (n, game)
}

/// The same game under the min-odd condition, which is normalized first.
fn random_min_odd(n: usize) -> (usize, MinOddParityGame) {
    let (_, game) = random_few(n);
    let arena: Arena = game.arena().clone();
    (n, MinOddParityGame::from_arena(arena))
}

macro_rules! solver_benchmarks {
    ($plain:ident, $min_odd:ident, $solve:ident) => {
        #[library_benchmark]
        #[bench::few_priorities_1000(args = (1_000), setup = random_few)]
        #[bench::few_priorities_4000(args = (4_000), setup = random_few)]
        #[bench::many_priorities_1000(args = (1_000), setup = random_many)]
        #[bench::many_priorities_4000(args = (4_000), setup = random_many)]
        #[bench::ladder_1000(args = (1_000), setup = ladder)]
        #[bench::ladder_4000(args = (4_000), setup = ladder)]
        fn $plain((n, game): (usize, MaxEvenParityGame)) -> usize {
            let solution = black_box(game.$solve().unwrap());
            black_box(solution.winning_region(Player::Eve).count()) + n
        }

        #[library_benchmark]
        #[bench::few_priorities_1000(args = (1_000), setup = random_min_odd)]
        #[bench::few_priorities_4000(args = (4_000), setup = random_min_odd)]
        fn $min_odd((n, game): (usize, MinOddParityGame)) -> usize {
            let solution = black_box(game.$solve().unwrap());
            black_box(solution.winning_region(Player::Eve).count()) + n
        }
    };
}

solver_benchmarks!(zielonka, zielonka_min_odd, solve_zielonka);
solver_benchmarks!(tangle_learning, tangle_learning_min_odd, solve);

library_benchmark_group!(
    name = game;
    benchmarks = zielonka, zielonka_min_odd, tangle_learning, tangle_learning_min_odd
);

main!(
    config = LibraryBenchmarkConfig::default().tool(Dhat::default()),
    library_benchmark_groups = game
);
