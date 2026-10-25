use thiserror::Error;

/// Errors returned by fallible operations of this crate.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum Error {
    /// The requested operation is not (yet) implemented for the given input.
    #[error("not yet implemented: {0}")]
    NotYetImplemented(&'static str),
}

/// Shorthand for results whose error type is [`enum@Error`].
pub type Result<T, E = Error> = std::result::Result<T, E>;
