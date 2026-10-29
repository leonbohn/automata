use crate::States;
use crate::Void;
use crate::alphabet::CharAlphabet;
use crate::automaton::Semantics;
use crate::automaton::semantics::observe_omega;
use crate::representation::{CollectTs, IntoTs};
use crate::ts::{Deterministic, StateIndex, SymbolOf};
use crate::word::OmegaWord;
use crate::word::ReducedOmegaWord;
use crate::{DTS, TransitionSystem, automaton::Automaton, ts::run};

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
        C: IntoTs + Clone,
    {
        self.clone()
            .map_edge_colors(|c| if c { 0 } else { 1 })
            .with_initial(self.initial)
            .into_dpa()
            .streamlined()
            .map_edge_colors(|c| {
                assert!(c == 0 || c == 1, "too many colors");
                c % 2 == 0
            })
            .collect_dba()
    }

    /// Tries to identify a word which is accepted by `self`. If such a word exists, it returns it and otherwise
    /// the function gives back `None`.
    pub fn give_word(&self) -> Option<ReducedOmegaWord<SymbolOf<Self>>> {
        for (_, good_scc) in self
            .sccs()
            .iter()
            .filter(|(_, scc)| !scc.is_empty() && self.is_reachable_from(self.initial, scc.first()))
        {
            if let Some(full_word) = good_scc.maximal_word() {
                // let InfinityColors(colors) = self
                //     .induced(&full_word, self.initial())
                //     .expect("word is valid");
                if let Some(infset) = self.visited_edge_colors_from(good_scc.first(), &full_word)
                    && infset.iter().any(|b| *b)
                {
                    let spoke = self
                        .word_from_to(self.initial, good_scc.first())
                        .expect("We know this is reachable!");
                    return Some(ReducedOmegaWord::ultimately_periodic(spoke, full_word));
                }
                // if colors.contains(&true) {
                //     let base = self
                //         .word_from_to(self.initial(), *good_scc.first().unwrap())
                //         .expect("we know this is reachable");
                //     return Some(OmegaWord::from_parts(base, full_word));
            }
        }
        None
    }

    /// Returns `true` if and only if `self` accepts a non-empty language.
    pub fn is_empty(&self) -> bool {
        self.give_word().is_none()
    }
}
