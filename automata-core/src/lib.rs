#[macro_use]
pub mod alphabet;

#[macro_use]
pub mod word;

pub mod math;
mod show;

pub mod dag;

pub mod kleene;

/// Alias for the default integer type that is used for coloring edges and states.
pub type Int = u8;

/// Represents the absence of a color. The idea is that this can be used when collecting
/// a transitions system as it can always be constructed from a color by simply forgetting it.
/// This is useful for example when we want to collect a transition system into a different
/// representation, but we don't care about the colors on the edges. In that case, the state
/// colors may be kept and the edge colors are dropped.
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct Void;

impl std::fmt::Debug for Void {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#")
    }
}

pub mod prelude {
    pub use super::dag;
    pub use super::math;
    pub use super::show::Show;
    pub use super::{Int, Void};
    pub use crate::alphabet;
    pub use crate::alphabet::{Alphabet, CharAlphabet, Expression, Matcher, Symbol};
    pub use crate::kleene::KleeneStar;
    pub use crate::upw;
    pub use crate::word::{
        self, FiniteWord, NormalizedOmegaWord, OmegaWord, PeriodicOmegaWord, ReducedOmegaWord, Word,
    };

    pub mod logging {
        pub fn init() {
            tracing_subscriber::util::SubscriberInitExt::init(
                tracing_subscriber::layer::SubscriberExt::with(
                    tracing_subscriber::registry(),
                    tracing_subscriber::Layer::with_filter(
                        tracing_subscriber::fmt::layer()
                            .pretty()
                            .with_writer(std::io::stderr),
                        tracing_subscriber::filter::EnvFilter::from_default_env(),
                    ),
                ),
            )
        }
    }
}
