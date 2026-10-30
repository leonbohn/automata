mod dense;
pub use dense::DenseTs;
mod det;
pub use det::Det;
pub(crate) mod linked;
pub use linked::{Compaction, LinkedTs};

/// The default type used to index states, `u32`.
pub type DefaultIdType = u32;
