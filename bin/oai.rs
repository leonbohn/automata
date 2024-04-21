use automata::hoa::input::HoaAutomatonStream;
use automata::prelude::*;

use tracing::info;
use tracing_subscriber::{filter, prelude::*};

pub fn main() {
    let stdout_log = tracing_subscriber::fmt::layer().pretty();

    tracing_subscriber::registry()
        .with(stdout_log.with_filter(filter::LevelFilter::TRACE))
        .init();

    info!("Reading from stdin");
    let mut stream = HoaAutomatonStream::new(std::io::stdin().lock());

    while let Some(aut) = stream.next() {
        info!("Read automaton with {} states", aut.size());
    }
}
