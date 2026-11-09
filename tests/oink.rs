//! Differential tests of `automata::game` against [Oink](https://github.com/trolando/oink), a
//! collection of parity game solvers. The flake provides it (`nix develop`); it is found through
//! the environment variable `OINK` or in the `PATH`. Without it the tests are skipped.
//!
//! Games are random, reproducible (fixed seeds) and written in the PGSolver format by
//! `ParityGame::to_pgsolver`. Oink solves max-even games, so the
//! other three conditions are checked by handing Oink the equivalent max-even priorities.

use automata::game::{
    MaxEvenParityGame, MaxOddParityGame, MinEvenParityGame, MinOddParityGame, Player,
};
use std::path::PathBuf;
use std::process::Command;

/// Priorities of the games are `0..=TOP`; `TOP` is even, which the min conditions rely on.
const TOP: u8 = 8;

fn oink() -> Option<PathBuf> {
    let path = std::env::var_os("OINK")
        .map(PathBuf::from)
        .unwrap_or("oink".into());
    Command::new(&path)
        .arg("--help")
        .output()
        .ok()
        .map(|_| path)
}

/// A small xorshift generator, so that the games are the same on every machine.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

/// A random total game: `(owner is Eve, priority, successors)` per vertex.
fn random_game(rng: &mut Rng) -> Vec<(bool, u8, Vec<usize>)> {
    let n = 1 + rng.below(40);
    (0..n)
        .map(|_| {
            let succ = (0..1 + rng.below(3)).map(|_| rng.below(n)).collect();
            (
                rng.below(2) == 0,
                rng.below(usize::from(TOP) + 1) as u8,
                succ,
            )
        })
        .collect()
}

/// Solves the game in the PGSolver format with Oink and returns, per vertex, whether Eve wins.
fn solve_with_oink(oink: &PathBuf, pg: &str, name: &str) -> Vec<bool> {
    let dir = std::env::temp_dir();
    let (input, output) = (
        dir.join(format!("{name}-{}.pg", std::process::id())),
        dir.join(format!("{name}-{}.sol", std::process::id())),
    );
    std::fs::write(&input, pg).unwrap();
    let status = Command::new(oink)
        .arg(&input)
        .arg(&output)
        .output()
        .expect("run oink");
    assert!(
        status.status.success(),
        "oink failed on {}",
        input.display()
    );
    let solution = std::fs::read_to_string(&output).unwrap();
    let _ = (std::fs::remove_file(&input), std::fs::remove_file(&output));

    // `paritysol n;` then `id winner [strategy]` per line, winner 0 is Eve
    let mut eve = vec![false; pg.lines().count() - 1];
    for line in solution.lines().skip(1) {
        let mut fields = line.trim_end_matches(';').split_whitespace();
        let v: usize = fields.next().unwrap().parse().unwrap();
        eve[v] = fields.next() == Some("0");
    }
    eve
}

macro_rules! differential {
    ($test:ident, $game:ident, $seed:literal, $rewrite:expr) => {
        #[test]
        fn $test() {
            let Some(oink) = oink() else {
                eprintln!("skipped: oink not found (set OINK or use `nix develop`)");
                return;
            };
            let mut rng = Rng($seed);
            for i in 0..200 {
                let game = random_game(&mut rng);

                // our game has the priorities of the condition, Oink gets max-even ones
                let rewrite: fn(u8) -> u8 = $rewrite;
                let mut ours = $game::new();
                let ids: Vec<_> = game
                    .iter()
                    .map(|&(eve, p, _)| {
                        ours.add_vertex(if eve { Player::Eve } else { Player::Adam }, p)
                    })
                    .collect();
                for (v, (_, _, succ)) in game.iter().enumerate() {
                    for &w in succ {
                        ours.add_edge(ids[v], ids[w]);
                    }
                }
                // the game as Oink gets it, written by the library
                let mut reference = MaxEvenParityGame::new();
                let ref_ids: Vec<_> = game
                    .iter()
                    .map(|&(eve, p, _)| {
                        reference
                            .add_vertex(if eve { Player::Eve } else { Player::Adam }, rewrite(p))
                    })
                    .collect();
                for (v, (_, _, succ)) in game.iter().enumerate() {
                    for &w in succ {
                        reference.add_edge(ref_ids[v], ref_ids[w]);
                    }
                }
                let expected = solve_with_oink(&oink, &reference.to_pgsolver(), stringify!($test));
                let solution = ours.solve().unwrap();
                for (v, id) in ids.iter().enumerate() {
                    assert_eq!(
                        solution.winner(*id) == Some(Player::Eve),
                        expected[v],
                        "game {i}, vertex {v}: {game:?}"
                    );
                }
            }
        }
    };
}

differential!(max_even, MaxEvenParityGame, 0x9e3779b97f4a7c15, |p| p);
differential!(max_odd, MaxOddParityGame, 0xd1b54a32d192ed03, |p| p + 1);
differential!(min_even, MinEvenParityGame, 0x2545f4914f6cdd1d, |p| TOP - p);
differential!(min_odd, MinOddParityGame, 0x94d049bb133111eb, |p| TOP - p
    + 1);
