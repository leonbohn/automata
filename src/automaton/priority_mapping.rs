use super::{FiniteWordAutomaton, MealyLike, Semantics, moore::MooreLike};
use crate::DTS;
use crate::ts::run::Observer;
use crate::ts::{EdgeColor, StateColor, run};
use automata_core::alphabet::CharAlphabet;
use automata_core::{Int, Void};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WeakPriorityMappingSemantics<const ON_EDGES: bool>;

impl<T: MooreLike> Semantics<T, false> for WeakPriorityMappingSemantics<false> {
    type Observer = run::LeastStateColor<T>;
    type Output = StateColor<T>;
    fn evaluate(&self, observed: <Self::Observer as Observer<T>>::Current) -> Self::Output {
        observed
    }
}
impl<T: MealyLike> Semantics<T, false> for WeakPriorityMappingSemantics<true> {
    type Observer = run::LeastEdgeColor<T>;
    type Output = EdgeColor<T>;
    fn evaluate(&self, observed: <Self::Observer as Observer<T>>::Current) -> Self::Output {
        observed
    }
}

/// Type alias for a weak priority mapping (longer words can only give more significant,
/// so smaller colors) where colors are emitted by states. The mapping is deterministic.
pub type StateBasedWeakPriorityMapping<A = CharAlphabet, D = DTS<A, Int, Void>> =
    FiniteWordAutomaton<A, WeakPriorityMappingSemantics<false>, Int, Void, true, D>;

/// Type alias for a weak priority mapping (longer words can only give more significant,
/// so smaller colors) where colors are emitted by edges. Crucially, this means that
/// the empty word emits no color. The mapping is deterministic.
pub type WeakPriorityMapping<A = CharAlphabet, D = DTS<A, Void, Int>> =
    FiniteWordAutomaton<A, WeakPriorityMappingSemantics<true>, Void, Int, true, D>;
