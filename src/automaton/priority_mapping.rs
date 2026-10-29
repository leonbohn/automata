use super::semantics::observe_finite;
use super::{Automaton, MealyLike, Semantics, moore::MooreLike};
use crate::DTS;
use crate::alphabet::CharAlphabet;
use crate::ts::run::Observer;
use crate::ts::{EdgeColor, StateColor, StateIndex, SymbolOf, run};
use crate::word::FiniteWord;
use crate::{Int, Void};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WeakPriorityMappingSemantics<const ON_EDGES: bool>;

impl<T: MooreLike, W: FiniteWord<Symbol = SymbolOf<T>>> Semantics<T, W>
    for WeakPriorityMappingSemantics<false>
{
    type Observer = run::LeastStateColor<T>;
    type Output = StateColor<T>;
    fn observe(
        &self,
        ts: &T,
        initial: StateIndex<T>,
        word: W,
    ) -> Option<<Self::Observer as Observer<T>>::Current> {
        observe_finite::<T, W, Self::Observer>(ts, initial, word)
    }
    fn evaluate(&self, observed: <Self::Observer as Observer<T>>::Current) -> Self::Output {
        observed
    }
}
impl<T: MealyLike, W: FiniteWord<Symbol = SymbolOf<T>>> Semantics<T, W>
    for WeakPriorityMappingSemantics<true>
{
    type Observer = run::LeastEdgeColor<T>;
    type Output = EdgeColor<T>;
    fn observe(
        &self,
        ts: &T,
        initial: StateIndex<T>,
        word: W,
    ) -> Option<<Self::Observer as Observer<T>>::Current> {
        observe_finite::<T, W, Self::Observer>(ts, initial, word)
    }
    fn evaluate(&self, observed: <Self::Observer as Observer<T>>::Current) -> Self::Output {
        observed
    }
}

/// Type alias for a weak priority mapping (longer words can only give more significant,
/// so smaller colors) where colors are emitted by states. The mapping is deterministic.
pub type StateBasedWeakPriorityMapping<T = DTS<CharAlphabet, Int, Void>> =
    Automaton<T, WeakPriorityMappingSemantics<false>>;

/// Type alias for a weak priority mapping (longer words can only give more significant,
/// so smaller colors) where colors are emitted by edges. Crucially, this means that
/// the empty word emits no color. The mapping is deterministic.
pub type WeakPriorityMapping<T = DTS<CharAlphabet, Void, Int>> =
    Automaton<T, WeakPriorityMappingSemantics<true>>;
