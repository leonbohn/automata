mod csr;
pub use csr::CsrTs;
mod dense;
pub use dense::DenseTs;
mod det;
pub use det::Det;
pub(crate) mod linked;
pub use linked::{Compaction, LinkedTs};

/// The default type used to index states, [`StateId`](crate::ts::StateId).
pub type DefaultIdType = crate::ts::StateId;
