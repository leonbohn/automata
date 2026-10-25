use thiserror::Error;

/// Errors that can occur when reading an automaton from the HOA format.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum HoaError {
    /// The input is not a valid (supported) HOA automaton.
    #[error("could not parse HOA automaton: {0}")]
    Parse(hoars::FromHoaError),
    /// The atomic propositions of the automaton cannot be represented.
    #[error("invalid atomic propositions: {0}")]
    Alphabet(#[from] crate::alphabet::PropAlphabetError),
    /// The identifiers of the states are not the contiguous numbers `0, 1, 2, ...`.
    #[error(
        "state with id {id} is at position {position}, state ids have to be the contiguous numbers 0, 1, 2, ..."
    )]
    StateOrder {
        /// The position in the body at which the state was found.
        position: usize,
        /// The identifier of the state.
        id: u32,
    },
    /// An edge or the initial condition has a conjunction of states, i.e. the automaton is alternating.
    #[error("alternating automata (conjunctions of states) are not supported")]
    UnsupportedAlternation,
    /// The automaton does not have exactly one initial state.
    #[error("expected exactly one initial state, found {0}")]
    UnsupportedStartStates(usize),
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
