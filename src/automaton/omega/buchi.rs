use crate::States;
use crate::alphabet::CharAlphabet;
use crate::automaton::semantics::observe_omega;
use crate::automaton::{DPA, Semantics};
use crate::representation::IntoTransitions;
use crate::ts::{Deterministic, StateIndex, SymbolOf};
use crate::word::OmegaWord;
use crate::{DTS, TransitionSystem, automaton::Automaton, ts::run};
use crate::{Int, Void};

/// Defines the [`Semantics`] of a deterministic Büchi automaton (DBA),
/// which is an acceptor of infinite words. It considers the set of
/// transitions which is taken infinitely often. If one of those is
/// colored with `true`, then the automaton accepts, while if all of the
/// transitions that are taken infinitely often are colored with `false`,
/// the automaton rejects.
///
/// This type will rarely be used on its own, for the automaton that makes
/// use of it, see [`DBA`].
#[derive(Debug, Default, Clone, Eq, PartialEq, Hash, Copy)]
pub struct BuchiCondition;

impl<T, W> Semantics<T, W> for BuchiCondition
where
    T: Deterministic<EdgeColor = bool>,
    W: OmegaWord<Symbol = SymbolOf<T>>,
{
    type Observer = run::GreatestEdgeColor<T>;
    type Output = bool;
    fn observe(
        &self,
        ts: &T,
        initial: StateIndex<T>,
        word: W,
    ) -> Option<<Self::Observer as run::Observer<T>>::Current> {
        observe_omega::<T, W, Self::Observer>(ts, initial, word)
    }
    fn evaluate(&self, observed: <Self::Observer as run::Observer<T>>::Current) -> Self::Output {
        observed
    }
}

/// A deterministic Büchi automaton (DBA) is a deterministic automaton with Büchi acceptance condition.
/// It accepts a word if it has a successful infinite run that takes an accepting
/// transition (i.e. one that is labeled with `true`) infinitely often.
///
/// In a certain sense, it is a special case of a deterministic parity automaton [`super::DPA`] with
/// min even and priorities 0 and 1.
pub type DBA<T = DTS<CharAlphabet, Void, bool>> = Automaton<T, BuchiCondition>;

impl<C> DBA<C>
where
    C: Deterministic<EdgeColor = bool> + States,
{
    /// Performs a streamlining operation akin to [`super::DPA::streamlined`].
    pub fn streamlined(&self) -> DBA<DTS<C::Alphabet, Void, bool>>
    where
        C: IntoTransitions<Initial = ()> + Clone,
    {
        let dpa: DPA<DTS<C::Alphabet, Void, Int>> = self
            .clone()
            .map_edge_colors(|c| if c { 0 } else { 1 })
            .erase_state_colors()
            .collect();
        dpa.streamlined()
            .map_edge_colors(|c| {
                assert!(c == 0 || c == 1, "too many colors");
                c % 2 == 0
            })
            .collect()
    }
}
