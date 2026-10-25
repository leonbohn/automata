use thiserror::Error;

/// Errors that can occur when reading an automaton from the HOA format.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum HoaError {
    /// The input is not a valid (supported) HOA automaton.
    #[error("could not parse HOA automaton: {0}")]
    Parse(hoars::FromHoaError),
    /// A parity automaton does not specify its number of acceptance sets.
    #[error("parity automaton without an Acceptance header item")]
    MissingAcceptanceSets,
    /// The acceptance condition (given by its name) is not supported.
    #[error("unsupported acceptance condition: {0}")]
    UnsupportedAcceptance(String),
    /// A label of an edge could not be converted into an expression over the atomic propositions.
    #[error("invalid edge label: {0}")]
    InvalidLabel(String),
    /// A deterministic automaton was requested, but the input is not deterministic.
    #[error("the automaton is not deterministic")]
    NotDeterministic,
    /// An error occurred while processing the part of the input in the given range.
    #[error("in range {start}..{end}: {source}")]
    InRange {
        /// Start of the range (byte offset).
        start: usize,
        /// End of the range (byte offset).
        end: usize,
        /// The underlying error.
        #[source]
        source: Box<HoaError>,
    },
}

impl From<hoars::FromHoaError> for HoaError {
    fn from(value: hoars::FromHoaError) -> Self {
        Self::Parse(value)
    }
}
