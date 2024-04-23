use automata::hoa::output::WriteHoa;
use automata::hoa::HoaAlphabet;
use automata::prelude::*;
use automata::{
    automaton::DeterministicOmegaAutomaton, hoa::input::FilterDeterministicHoaAutomatonStream,
};

use tracing::{debug, info, trace};
use tracing_subscriber::{filter, prelude::*};

use clap::{Arg, ArgAction, ArgMatches, Command};

fn cli() -> clap::Command {
    Command::new("oai")
    .about("Omega automata interaction")
    .subcommand_required(true)
    .arg(
        Arg::new("verbosity")
        .short('v')
        .long("verbosity")
        .num_args(0..=1)
        .require_equals(true)
        .value_parser(["info", "debug", "trace"])
        .default_missing_value("info")
    )
    .subcommand(
        Command::new("todpa")
        .about("reads HOA automaton from stdin and tries to convert it into a deterministic parity automaton")
    )
}

fn setup_logging(matches: &ArgMatches) {
    let Ok(Some(verbosity)) = matches.try_get_one::<String>("verbosity") else {
        return;
    };

    let level = match verbosity.as_str() {
        "trace" => filter::LevelFilter::TRACE,
        "debug" => filter::LevelFilter::DEBUG,
        "info" => filter::LevelFilter::INFO,
        _ => unreachable!(),
    };

    let stdout_log = tracing_subscriber::fmt::layer()
        .pretty()
        .with_writer(std::io::stderr);

    tracing_subscriber::registry()
        .with(stdout_log.with_filter(level))
        .init();

    trace!("setup {level} logging");
}

pub fn main() {
    let matches = cli().get_matches();

    setup_logging(&matches);

    info!("reading automata from stdin");
    let mut stream = FilterDeterministicHoaAutomatonStream::new(std::io::stdin().lock());

    match matches.subcommand() {
        Some(("todpa", sub_matches)) => {
            info!("converting input automata into DPAs");

            while let Some(aut) = stream.next() {
                info!("read deterministic automaton with {} states", aut.size());

                let converted: DeterministicOmegaAutomaton<CharAlphabet> = aut.into();
                trace!("first conversion successful");
                let reconverted: DeterministicOmegaAutomaton<HoaAlphabet> =
                    converted.try_into().unwrap();

                print!("{}", reconverted.into_dpa().to_hoa());
            }
        }
        _ => unreachable!(),
    }
}
