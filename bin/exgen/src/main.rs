use automata::automaton::NBA;
use automata::core::alphabet::{Alphabet, CharAlphabet};
use automata::core::Void;
use automata::dot::Dottable;
use automata::ts::{DefaultIdType, Sproutable};
use automata::TransitionSystem;
use automata_core::math::Set;
use clap::Parser;
use rand::Rng;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::Layer;

#[derive(Debug, Clone, clap::Parser)]
struct Cli {
    #[clap(short = 's', long, default_value = "2")]
    alphabet_size: usize,
    #[clap(short = 'q', long, default_value = "3")]
    num_states: usize,
    #[clap(short = 't', long, default_value = "0.5")]
    transition_probability: f32,
    #[clap(short = 'f', long, default_value = "0.3")]
    accepting_state_probability: f32,
    #[clap(short = 'n', long, default_value = "1")]
    num_automata: usize,
    #[clap(short = 'd', long)]
    display_each: bool,
}

fn random_nba(
    alphabet_size: usize,
    num_states: usize,
    transition_probability: f32,
    accepting_state_probability: f32,
) -> NBA {
    let alphabet = CharAlphabet::of_size(alphabet_size);
    let universe = alphabet.universe().collect::<Vec<_>>();

    let mut rng = rand::thread_rng();
    let mut states = vec![];

    for _i in 0..num_states {
        let accepting = rng.gen_bool(accepting_state_probability as f64);
        states.push(accepting);
    }

    let mut nba = NBA::from_state_colors(alphabet, states);

    for i in 0..num_states {
        for j in 0..num_states {
            for sym in &universe {
                if rng.gen_bool(transition_probability as f64) {
                    nba.add_edge((i as DefaultIdType, *sym, Void, j as DefaultIdType));
                }
            }
        }
    }

    nba.add_initial_state(0);

    nba
}

#[derive(Debug, Clone)]
struct NBAGenerator {
    failed_attempts: usize,
    alphabet: CharAlphabet,
    num_states: usize,
    transition_probability: f32,
    accepting_state_probability: f32,
}

impl Iterator for NBAGenerator {
    type Item = NBA;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            self.failed_attempts += 1;
            if self.failed_attempts > 1000 {
                panic!("failed to generate NBA, maybe it's impossible")
            }

            let mut nba = random_nba(
                self.alphabet.size(),
                self.num_states,
                self.transition_probability,
                self.accepting_state_probability,
            );

            let removed = nba.trim();
            if !removed.is_empty() {
                continue;
            }

            if nba.state_indices_with_color().all(|(_, b)| !b) {
                continue;
            }

            self.failed_attempts = 0;
            return Some(nba);
        }
    }
}

impl NBAGenerator {
    fn new(
        alphabet: CharAlphabet,
        num_states: usize,
        transition_probability: f32,
        accepting_state_probability: f32,
    ) -> Self {
        Self {
            failed_attempts: 0,
            alphabet,
            num_states,
            transition_probability,
            accepting_state_probability,
        }
    }
}

fn pause() {
    use std::io::prelude::*;
    let mut stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    write!(stdout, "press ENTER to continue").unwrap();
    stdout.flush().unwrap();
    let _ = stdin.read(&mut [0u8]).unwrap();
}

fn main() {
    // setup logging from environment variable
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::layer()
                .pretty()
                .with_writer(std::io::stderr)
                .with_filter(tracing_subscriber::filter::LevelFilter::TRACE),
        )
        .init();

    let cli = Cli::parse();
    let mut gen = NBAGenerator::new(
        CharAlphabet::of_size(cli.alphabet_size),
        cli.num_states,
        cli.transition_probability,
        cli.accepting_state_probability,
    );

    let start = std::time::Instant::now();
    for i in 1..100 {
        let nba = gen.next().unwrap();

        let det = automata::determinization::nbadet(nba.clone());

        if det.size() > 9 {
            continue;
        }
        if det.size() < 5 {
            continue;
        }

        let mut macrostates = det
            .state_indices_with_color()
            .map(|(_, c)| c)
            .collect::<Vec<_>>();
        macrostates.dedup();

        let mut swapped = false;
        let mut otherranked = false;

        'outer: for i in 0..macrostates.len() {
            let states = macrostates[i].partition();
            let ranks = macrostates[i].ranks();

            for j in i + 1..macrostates.len() {
                let other_states = macrostates[j].partition();
                let other_ranks = macrostates[j].ranks();

                if states == other_states && ranks != other_ranks {
                    otherranked = true;
                }
                if states != other_states
                    && macrostates[i].flat_partition() == macrostates[j].flat_partition()
                {
                    swapped = true;
                }
            }
        }

        if !swapped || !otherranked {
            continue;
        }

        nba.display_rendered().unwrap();
        det.display_rendered().unwrap();
        println!("{:?}", macrostates);
        break;
    }
}
