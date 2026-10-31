use crate::ts::Sccs;
use crate::ts::States;
use crate::ts::{DenseId, EdgeId, Sproutable};
use std::{collections::BTreeSet, fmt::Debug, hash::Hash};

use crate::automaton::problems::search;
use crate::automaton::semantics::observe_omega;
use crate::automaton::{Automaton, Equivalence, Semantics};
use crate::math;
use crate::representation::IntoTransitions;
use crate::ts::operations::{Product, ProductIndex};
use crate::ts::{Deterministic, EdgeColor, Shrinkable, StateIndex, SymbolOf, operations};
use crate::word::OmegaWord;
use crate::{DTS, Pointed, TransitionSystem, ts::run};
use crate::{
    Int, Show, Void,
    alphabet::CharAlphabet,
    partition::Partition,
    word::{FiniteWord, ReducedOmegaWord},
};
use itertools::Itertools;
use tracing::trace;

/// A deterministic parity automaton (DPA). It uses a [`DTS`]
/// as its transition system and an [`Int`] as its edge color.
/// The acceptance condition is given by the type `Sem`, which
/// defaults to [`MinEvenParityCondition`], meaning the automaton accepts
/// if the least color that appears infinitely often during
/// a run is even.
pub type DPA<T = DTS<CharAlphabet, Void, Int>, Sem = MinEvenParityCondition> = Automaton<T, Sem>;

/// Represents a min even parity condition which accepts if and only if the least color
/// that labels a transition that is taken infinitely often, is even. For the automaton
/// type that makes use of this semantics, see [`DPA`].
///
/// Other (equivalent) types of parity conditions, that consider the maximal seen color
/// or demand that the minimal/maximal recurring color are odd, are defined as
/// [`MaxEvenParityCondition`], [`MinOddParityCondition`] and [`MaxOddParityCondition`],
/// respectively.
#[derive(Clone, Debug, Default, Copy, Hash, Eq, PartialEq)]
pub struct MinEvenParityCondition;

/// Defines a [`Semantics`] that outputs `true` if the *maximum* color/priority that
/// appears infinitely often is *even*. See also [`MinEvenParityCondition`].
#[derive(Clone, Debug, Default, Copy, Hash, Eq, PartialEq)]
pub struct MaxEvenParityCondition;
/// Defines a [`Semantics`] that outputs `true` if the *minimum* color/priority that
/// appears infinitely often is *odd*. See also [`MinEvenParityCondition`].
#[derive(Clone, Debug, Default, Copy, Hash, Eq, PartialEq)]
pub struct MinOddParityCondition;
/// Defines a [`Semantics`] that outputs `true` if the *maximum* color/priority that
/// appears infinitely often is *odd*. See also [`MinEvenParityCondition`].
#[derive(Clone, Debug, Default, Copy, Hash, Eq, PartialEq)]
pub struct MaxOddParityCondition;

/// Implements [`Semantics`] for a parity condition. The edge color limit that is observed
/// is the minimum or maximum, depending on `$max`, and the word is accepted if the parity
/// of the limit is as given.
macro_rules! parity_semantics {
    ($cond:ident, $max:literal, $even:literal) => {
        impl<T, W> Semantics<T, W> for $cond
        where
            T: Deterministic<EdgeColor = Int>,
            W: OmegaWord<Symbol = SymbolOf<T>>,
        {
            type Output = bool;
            type Observer = run::EdgeColorLimit<T, $max>;
            fn observe(
                &self,
                ts: &T,
                initial: StateIndex<T>,
                word: W,
            ) -> Option<<Self::Observer as run::Observer<T>>::Current> {
                observe_omega::<T, W, Self::Observer>(ts, initial, word)
            }
            fn evaluate(
                &self,
                observed: <Self::Observer as run::Observer<T>>::Current,
            ) -> Self::Output {
                observed.is_multiple_of(2) == $even
            }
        }
    };
}
parity_semantics!(MinEvenParityCondition, false, true);
parity_semantics!(MaxEvenParityCondition, true, true);
parity_semantics!(MinOddParityCondition, false, false);
parity_semantics!(MaxOddParityCondition, true, false);

impl<D> DPA<D>
where
    D: Deterministic<EdgeColor = Int> + States,
{
    /// Verifies whether or not the unerlying transition system represents an
    /// informative right congruence or not. Specifically, this means that
    /// any two distinct states can be distinguished from each other by a word
    /// which is accepted starting from one of the two states but not starting
    /// from the other.
    ///
    /// # Example
    /// ```
    /// use automata::ts::{Sproutable, Builder};
    ///
    /// let mut dpa = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', 0, 1), (0, 'b', 1, 1),
    ///                        (1, 'a', 0, 0), (1, 'b', 3, 0)])
    ///     .into_dpa(0);
    /// assert!(!dpa.is_informative_right_congruent());
    ///
    /// dpa.add_edge((0, 'c', 2, 0));
    /// dpa.add_edge((1, 'c', 1, 1));
    /// assert!(dpa.is_informative_right_congruent());
    /// ```
    pub fn is_informative_right_congruent(&self) -> bool {
        self.prefix_partition().iter().all(|c| {
            debug_assert!(!c.is_empty(), "classes are never empty");
            c.len() == 1
        })
    }

    /// Creates a streamlined version of `self`, that is DPA where the edge colors are
    /// normalized and the transition structure is minimized as a Mealy machine.
    ///
    /// This method is just a thin wrapper that first calls [`Self::normalized`] to
    /// normalize the priorities and subsequently runs a mealy partition refinement
    /// algorithm to obtain a minimal quotient automaton.
    ///
    /// # Example
    /// ```
    /// use automata::ts::{Deterministic, Builder, States, TransitionSystem};
    ///
    /// let dpa = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', 0, 0), (0, 'b', 1, 0)])
    ///     .into_dpa(0);
    /// let streamlined = dpa.streamlined();
    /// assert_eq!(dpa.state_count(), streamlined.state_count());
    ///
    /// let dpa = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', 0, 1), (0, 'b', 1, 1),
    ///                        (1, 'a', 0, 0), (1, 'b', 3, 0)])
    ///     .into_dpa(0);
    /// assert_eq!(dpa.run("ab").last_edge_color(), Some(3));
    /// let streamlined = dpa.streamlined();
    /// assert_eq!(streamlined.state_count(), 1);
    /// assert_eq!(streamlined.run("ab").last_edge_color(), Some(1))
    /// ```
    pub fn streamlined(&self) -> DPA<DTS<D::Alphabet, Void, Int>>
    where
        EdgeColor<Self>: Eq + Hash + Clone + Ord,
        D: Clone + IntoTransitions<Initial = ()>,
    {
        let minimized = crate::minimization::partition_refinement::mealy_partition_refinement(
            self.normalized(),
        );
        minimized.erase_state_colors().collect()
    }

    /// Computes the least and greatest edge color that appears on any edge of the automaton.
    /// If there are no edges, `(Int::MAX, 0)` is returned.
    pub fn low_and_high_priority(&self) -> (Int, Int) {
        self.edge_colors_unique()
            .fold((Int::MAX, 0), |(low, high), c| (low.min(c), high.max(c)))
    }

    /// Gives a witness for the fact that the language accepted by `self` is not universal. This is
    /// done by finding a rejecting cycle in the underlying transition system.
    /// # Example
    /// ```
    /// use automata::ts::{Deterministic, Builder, TransitionSystem};
    ///
    /// let dpa = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', 0, 0), (0, 'b', 1, 0)])
    ///     .into_dpa(0);
    /// assert!(dpa.give_rejected_word().is_some());
    ///
    /// let univ = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', 0, 0), (0, 'b', 2, 0)])
    ///     .into_dpa(0);
    /// assert!(univ.give_rejected_word().is_none())
    /// ```
    pub fn give_rejected_word(&self) -> Option<ReducedOmegaWord<SymbolOf<Self>>> {
        self.colors().find_map(|i| {
            if i % 2 == 0 {
                None
            } else {
                self.witness_color(i)
            }
        })
    }

    /// Builds the complement of `self`, i.e. the DPA that accepts the complement of the language
    /// accepted by `self`.
    ///
    /// The complement is obtained by flipping the parity of every priority, which means shifting
    /// all priorities by one. To make sure that this cannot overflow, the priorities are always
    /// [normalized](Self::normalized) first. This yields the minimal number of distinct
    /// priorities, so the shift only fails if all of the `Int::MAX + 1` priorities `0..=Int::MAX`
    /// are needed. If the least priority of the normalized automaton is positive, we shift down
    /// instead of up, which cannot fail.
    ///
    /// Note that normalizing is more expensive than just shifting the priorities. If you do not
    /// want this, use [`Self::complement_without_normalizing`].
    ///
    /// # Panics
    /// Panics if the complement cannot be represented, i.e. if the language needs `Int::MAX + 1`
    /// distinct priorities, beginning at 0. Such an automaton has at least that many states.
    pub fn complement(self) -> DPA<DTS<D::Alphabet, Void, Int>>
    where
        EdgeColor<Self>: Eq + Hash + Clone + Ord,
        D: Clone + IntoTransitions<Initial = ()>,
    {
        let mut complement = self.normalized();
        let (low, high) = complement.low_and_high_priority();
        // the normalized priorities are minimal, so shifting up only fails if all of them are used
        if low > 0 {
            complement.map_edge_colors_in_place(|c| *c -= 1);
        } else if high < Int::MAX {
            complement.map_edge_colors_in_place(|c| *c += 1);
        } else {
            panic!(
                "cannot complement a DPA that needs all priorities 0..={}",
                Int::MAX
            );
        }
        complement
    }

    /// Builds the complement of `self` by shifting all priorities by one, without normalizing
    /// them first. This is cheap, but the priorities of the result are only as small as those of
    /// `self`. Prefer [`Self::complement`] unless you know that the priorities are already
    /// normalized or want to keep them as they are.
    ///
    /// If the least priority is positive, all priorities are shifted down by one, otherwise they
    /// are shifted up by one. Returns `None` if the latter is necessary but impossible, which
    /// is the case if both `0` and `Int::MAX` occur as priorities.
    ///
    /// # Example
    /// ```
    /// use automata::ts::{Deterministic, Builder, TransitionSystem};
    ///
    /// let dpa = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', 255, 0), (0, 'b', 254, 0)])
    ///     .into_dpa(0);
    /// let complement = dpa.complement_without_normalizing().unwrap();
    /// assert_eq!(complement.low_and_high_priority(), (253, 254));
    ///
    /// let dpa = Builder::without_state_colors()
    ///     .with_transitions([(0, 'a', 255, 0), (0, 'b', 0, 0)])
    ///     .into_dpa(0);
    /// assert!(dpa.complement_without_normalizing().is_none());
    /// ```
    pub fn complement_without_normalizing(self) -> Option<DPA<DTS<D::Alphabet, Void, Int>>>
    where
        D: IntoTransitions<Initial = ()>,
    {
        let (low, high) = self.low_and_high_priority();
        if low > 0 {
            // also covers the case of no edges, where `low == Int::MAX`
            Some(
                self.map_edge_colors(|c| c - 1)
                    .erase_state_colors()
                    .collect(),
            )
        } else if high < Int::MAX {
            Some(
                self.map_edge_colors(|c| c + 1)
                    .erase_state_colors()
                    .collect(),
            )
        } else {
            None
        }
    }

    /// Gives a witness for the fact that `left` and `right` are not language-equivalent. This is
    /// done by finding a separating word, i.e. a word that is accepted from one of the two states
    /// but not by the other.
    pub fn separate(
        &self,
        p: StateIndex<Self>,
        q: StateIndex<Self>,
    ) -> Option<ReducedOmegaWord<SymbolOf<Self>>> {
        if p == q {
            return None;
        }

        let (from_p, from_q) = (DPA::from_parts(self, p), DPA::from_parts(self, q));
        Equivalence::of(&from_p).and(&from_q).counterexample()
    }

    /// Computes a [`Partition`] of the reachable state indices of `self` such that any two states
    /// in the same class of the partition are language-equivalent.
    ///
    /// Two states are not equivalent if and only if, in the product of `self` with itself, the
    /// pair of them can reach a cycle that is accepted by exactly one of the components. These
    /// pairs are found for all pairs at once: first the cycles are located by decomposing the
    /// product into strongly connected components, then everything that reaches one of them is
    /// marked by a backwards search.
    pub fn prefix_partition(&self) -> Partition<D::StateIndex> {
        let states: math::FxIndexSet<_> = self.reachable_state_indices().collect();
        let n = states.len();
        debug_assert_eq!(states.get_index(0), Some(&self.initial()));
        let id = |ProductIndex(p, q): ProductIndex<_, _>| {
            states.get_index_of(&p).expect("reachable") * n
                + states.get_index_of(&q).expect("reachable")
        };

        let product = self.ts_product(self);
        let pairs: Vec<_> = states
            .iter()
            .flat_map(|&p| states.iter().map(move |&q| ProductIndex(p, q)))
            .collect();
        let mut predecessors = vec![Vec::new(); n * n];
        for &pair in &pairs {
            for edge in product.edges_from(pair).expect("reachable") {
                predecessors[id(edge.target())].push(id(pair));
            }
        }

        let mut separated = vec![false; n * n];
        let mut todo = Vec::new();
        for accepted in [(true, false), (false, true)] {
            search(
                &product,
                pairs.clone(),
                &|&c| c,
                accepted,
                (0, 0),
                |scc, _| {
                    for &pair in scc.state_indices() {
                        todo.push(id(pair));
                    }
                    None
                },
            );
        }
        while let Some(pair) = todo.pop() {
            if !std::mem::replace(&mut separated[pair], true) {
                todo.extend(&predecessors[pair]);
            }
        }

        let mut classes: Vec<(usize, BTreeSet<_>)> = Vec::new();
        for (i, &q) in states.iter().enumerate() {
            match classes.iter_mut().find(|(rep, _)| !separated[rep * n + i]) {
                Some((_, class)) => {
                    class.insert(q);
                }
                None => classes.push((i, BTreeSet::from_iter([q]))),
            }
        }
        classes
            .into_iter()
            .map(|(_, class)| class)
            .collect::<Vec<_>>()
            .into()
    }

    /// Builds the quotient of `self` with respect to the prefix partition. This will result in the prefix
    /// congruence that underlies the language accepted by `self`.
    pub fn prefix_congruence(&self) -> operations::Quotient<&Self> {
        self.quotient(self.prefix_partition())
    }

    /// Attempts to find an omega-word that witnesses the given `color`, meaning the least color that
    /// appears infinitely often during the run of the returned word is equal to `color`. If no such
    /// word exists, `None` is returned.
    pub fn witness_color(&self, color: Int) -> Option<ReducedOmegaWord<SymbolOf<Self>>> {
        let restrict = self.edge_color_restricted(color, Int::MAX);
        let sccs = Sccs::on(&restrict).compute();
        for (_, scc) in sccs.iter() {
            if scc.is_transient() {
                continue;
            }
            if scc.interior_edge_colors().any(|c| c == color) {
                // components that cannot be reached from the initial state have no representative
                let Some(rep) = scc.minimal_representative() else {
                    continue;
                };
                let cycle = scc
                    .maximal_loop_from(rep.state_index())
                    .expect("This thing is non-transient");
                return Some(ReducedOmegaWord::ultimately_periodic(
                    rep.collect_vec(),
                    cycle,
                ));
            }
        }
        None
    }

    /// Returns an iterator over all colors that appear on edges of `self`.
    pub fn colors(&self) -> impl Iterator<Item = Int> + '_ {
        self.states()
            .flat_map(|q| self.edges_from(q).into_iter().flatten().map(|e| *e.color()))
            .unique()
    }

    /// Produces a DPA that is language-equivalent to `self` but has the minimal number of different colors. This
    /// done by a procedure which in essence was first introduced by Carton and Maceiras in their paper
    /// "Computing the rabin index of a finite automaton". The procedure that this implementation actually uses
    /// is outlined by Schewe and Ehlers in [Natural Colors of Infinite Words](https://arxiv.org/pdf/2207.11000.pdf)
    /// in Section 4.1, Definition 2.
    ///
    /// The `expect`s and assertions in the implementation check invariants of the procedure (for
    /// example that the edges of the shrinking copy of the system are the ones that were
    /// collected) and do not depend on the input.
    pub fn normalized(&self) -> DPA<DTS<D::Alphabet, Void, Int>>
    where
        EdgeColor<Self>: Eq + Hash + Clone + Ord,
        D: Clone + IntoTransitions<Initial = ()>,
        // StateColor<Self>: Eq + Hash + Clone + Ord,
    {
        let start = std::time::Instant::now();

        let (out, numbering): (DTS<D::Alphabet, Void, D::EdgeColor>, _) =
            self.ts.clone().erase_state_colors().collect_with_map();
        let out_initial = StateIndex::<DTS<D::Alphabet, Void, D::EdgeColor>>::from_usize(
            numbering
                .id(&self.initial)
                .expect("the initial state is a state"),
        );
        // `ts` is shrunk while we work, `out` keeps all edges. Both use the same edge ids, so the new
        // priority of an edge is stored in a table that is indexed by its id.
        let mut ts = out.clone();
        let mut recoloring: Vec<Option<Int>> = vec![None; out.edge_bound()];
        let id_of = |e: &crate::ts::EdgeRef<'_, _, _, _>| -> usize {
            e.id().expect("edges of a storage have an id").into_usize()
        };

        let mut remove_states = Vec::new();
        let mut remove_edges: Vec<EdgeId> = Vec::new();

        let mut priority = 0;
        'outer: loop {
            for id in remove_edges.drain(..) {
                assert!(
                    ts.remove_edge(id).is_some(),
                    "We must be able to actually remove these edges"
                );
            }
            for state in remove_states.drain(..) {
                trace!("removing state {state}");
                debug_assert!(
                    ts.edges_from(state)
                        .unwrap()
                        .all(|e| recoloring[id_of(&e)].is_some()),
                    "every edge of a removed state must have been recolored"
                );
                assert!(
                    ts.remove_state(state).is_some(),
                    "We must be able to actually remove these edges"
                );
            }

            if ts.state_count() == 0 {
                trace!("no states left, terminating");
                break 'outer;
            }

            let dag = Sccs::on(&ts).compute();

            'inner: for (_, scc) in dag.iter() {
                trace!("inner priority {priority} | scc {:?}", scc);
                if scc.is_transient() {
                    trace!("scc {:?} is transient", scc);
                    for state in scc.iter() {
                        for edge in ts.edges_from(*state).unwrap() {
                            trace!(
                                "recoloring and removing {state:?} --{}|{}--> {:?} with priority {}",
                                edge.expression().show(),
                                edge.color().show(),
                                edge.target(),
                                priority
                            );
                            recoloring[id_of(&edge)] = Some(priority);
                            remove_edges.push(edge.id().expect("edges of a storage have an id"));
                        }
                        remove_states.push(*state);
                    }
                    continue 'inner;
                }

                // the edges leaving the scc get the current priority, the others are interior
                let mut minimal_interior_edge_color = None;
                for q in scc.iter() {
                    for edge in ts.edges_from(*q).unwrap() {
                        if scc.contains(&edge.target()) {
                            let color = *edge.color();
                            minimal_interior_edge_color = Some(
                                minimal_interior_edge_color.map_or(color, |m: Int| m.min(color)),
                            );
                        } else {
                            trace!(
                                "recoloring border edge {q} --{}--> {} with prio {priority}",
                                edge.expression().show(),
                                edge.target()
                            );
                            recoloring[id_of(&edge)] = Some(priority);
                        }
                    }
                }
                let minimal_interior_edge_color =
                    minimal_interior_edge_color.expect("We know this is not transient");

                if priority % 2 != minimal_interior_edge_color % 2 {
                    trace!("minimal interior priority: {minimal_interior_edge_color}, skipping");
                    continue 'inner;
                }

                trace!(
                    "minimal interior priority: {minimal_interior_edge_color}, recoloring edges"
                );
                for q in scc.iter() {
                    for edge in ts.edges_from(*q).unwrap() {
                        if scc.contains(&edge.target())
                            && *edge.color() == minimal_interior_edge_color
                        {
                            trace!(
                                "recolouring and removing {q:?} --{}|{}--> {:?} with priority {}",
                                edge.expression().show(),
                                edge.color().show(),
                                edge.target(),
                                priority
                            );
                            recoloring[id_of(&edge)] = Some(priority);
                            remove_edges.push(edge.id().expect("edges of a storage have an id"));
                        }
                    }
                }
            }

            if remove_edges.is_empty() {
                priority += 1;
            }
        }

        trace!("computation done, building output automaton");
        let mut out = out;
        for id in 0..out.edge_bound() {
            let id = EdgeId::from_usize(id);
            let Some(slot) = out.edge_color_mut(id) else {
                continue;
            };
            *slot = recoloring[id.into_usize()]
                .unwrap_or_else(|| panic!("Could not find recoloring for edge {id}"));
        }
        let ret: DPA<DTS<D::Alphabet, Void, Int>> = DPA::from_parts(out, out_initial);

        tracing::debug!("normalizing DPA took {} μs", start.elapsed().as_micros());

        debug_assert!(Equivalence::of(self).and(&ret).holds());
        ret
    }
}

#[cfg(test)]
mod tests {
    use super::DPA;
    use crate::States;
    use crate::Void;
    use crate::automaton::{Emptiness, Equivalence, Inclusion};
    use crate::representation::CollectPointed;
    use crate::ts::operations::Product;
    use crate::ts::{Builder, Deterministic};
    use crate::{DTS, Pointed, RightCongruence, TransitionSystem};

    #[test]
    fn normalize_dpa() {
        let dpa = DTS::builder()
            .default_color(Void)
            .with_transitions([
                (0, 'a', 2, 0),
                (0, 'b', 1, 1),
                (1, 'a', 0, 0),
                (1, 'b', 1, 1),
            ])
            .into_dpa(0);
        let normalized = dpa.normalized();
        assert!(Equivalence::of(&normalized).and(&dpa).holds());

        for (input, expected) in [("a", 0), ("b", 0), ("ba", 0), ("bb", 1)] {
            assert_eq!(normalized.run(input).last_edge_color(), Some(expected))
        }
    }

    fn example_dpa() -> DPA {
        DTS::builder()
            .default_color(Void)
            .with_transitions([
                (0, 'a', 0, 0),
                (0, 'b', 1, 1),
                (0, 'c', 2, 2),
                (1, 'a', 3, 2),
                (1, 'b', 4, 2),
                (1, 'c', 7, 1),
                (2, 'a', 2, 0),
                (2, 'b', 5, 0),
                (2, 'c', 6, 0),
            ])
            .into_dpa(0)
    }

    #[test]
    fn complement_with_maximal_priority() {
        // priorities 254 and 255 normalize to 0 and 1
        let dpa = Builder::without_state_colors()
            .with_transitions([(0, 'a', 254, 0), (0, 'b', 255, 0)])
            .into_dpa(0);
        let complement = dpa.clone().complement();
        assert!(!Equivalence::of(&complement).and(&dpa).holds());
        assert!(
            Equivalence::of(&complement.clone().complement())
                .and(&dpa)
                .holds()
        );
        assert_eq!(complement.low_and_high_priority(), (1, 2));

        // every run is rejecting, so the complement is universal. All priorities are positive
        // here, so the complement shifts down instead of up.
        let dpa = Builder::without_state_colors()
            .with_transitions([(0, 'a', 1, 0), (0, 'b', 255, 0)])
            .into_dpa(0);
        let complement = dpa.complement();
        assert!(complement.give_rejected_word().is_none());
        assert!(Emptiness::of(&complement).witness().is_some());
    }

    #[test]
    fn complement_without_normalizing_keeps_priorities() {
        let dpa = Builder::without_state_colors()
            .with_transitions([(0, 'a', 254, 0), (0, 'b', 255, 0)])
            .into_dpa(0);
        let complement = dpa.clone().complement_without_normalizing().unwrap();
        assert_eq!(complement.low_and_high_priority(), (253, 254));
        assert!(Equivalence::of(&complement).and(&dpa.complement()).holds());

        let dpa = Builder::without_state_colors()
            .with_transitions([(0, 'a', 0, 0), (0, 'b', 255, 0)])
            .into_dpa(0);
        assert!(dpa.complement_without_normalizing().is_none());
    }

    #[test]
    fn dpa_priority_restriction() {
        let dpa = example_dpa();
        assert_eq!(dpa.edges_from(0).unwrap().count(), 3);
        let d05 = dpa.as_ref().edge_color_restricted(0, 5);
        let d13 = dpa.as_ref().edge_color_restricted(1, 3);
        assert_eq!(d05.edges_from(2).unwrap().count(), 2);
        assert_eq!(d13.edges_from(1).unwrap().count(), 1);
        assert_eq!(d13.edges_from(2).unwrap().count(), 1);
        assert_eq!(d13.edges_from(0).unwrap().count(), 2);
    }

    #[test]
    fn dpa_equivalences() {
        let good = [
            DTS::builder()
                .default_color(Void)
                .with_transitions([
                    (0, 'a', 0, 1),
                    (0, 'b', 1, 0),
                    (1, 'a', 1, 1),
                    (1, 'b', 0, 0),
                ])
                .into_dpa(0),
            DTS::builder()
                .default_color(Void)
                .with_transitions([
                    (0, 'a', 5, 1),
                    (0, 'b', 7, 0),
                    (1, 'a', 3, 1),
                    (1, 'b', 2, 2),
                    (2, 'a', 3, 0),
                    (2, 'b', 5, 2),
                ])
                .into_dpa(0),
        ];
        let bad = [
            DTS::builder()
                .default_color(Void)
                .with_transitions([(0, 'a', 1, 0), (0, 'b', 0, 0)])
                .into_dpa(0),
            DTS::builder()
                .default_color(Void)
                .with_transitions([(0, 'a', 1, 0), (0, 'b', 2, 0)])
                .into_dpa(0),
            DTS::builder()
                .default_color(Void)
                .with_transitions([
                    (0, 'a', 4, 1),
                    (0, 'b', 1, 0),
                    (1, 'a', 5, 0),
                    (1, 'b', 3, 1),
                ])
                .into_dpa(0),
        ];

        let l = &good[0];
        let r = &bad[2];
        let prod = l.ts_product(r).reachable_part();
        let _sccs = crate::ts::Sccs::on(&prod).compute();
        assert!(!Equivalence::of(&good[0]).and(&bad[2]).holds());

        for g in &good {
            for b in &bad {
                assert!(!Equivalence::of(g).and(b).holds());
            }
        }
    }

    #[test]
    fn dpa_run() {
        let dpa = DTS::builder()
            .with_transitions([
                (0, 'a', 1, 1),
                (0, 'b', 1, 0),
                (0, 'c', 1, 0),
                (1, 'a', 0, 0),
                (1, 'b', 1, 0),
                (1, 'c', 1, 0),
            ])
            .default_color(Void)
            .into_dpa(0);
        assert!(!dpa.accepts(upw!("cabaca")))
    }

    #[test]
    fn dpa_inclusion() {
        let univ = DTS::builder()
            .default_color(Void)
            .with_transitions([(0, 'a', 0, 0), (0, 'b', 2, 0)])
            .into_dpa(0);
        let aomega = DTS::builder()
            .default_color(Void)
            .with_transitions([(0, 'a', 0, 0), (0, 'b', 1, 0)])
            .into_dpa(0);
        assert!(Inclusion::of(&aomega).within(&univ).holds());
        assert!(!Inclusion::of(&univ).within(&aomega).holds());
    }

    #[test]
    fn dpa_equivalence_clases() {
        let dpa = DTS::builder()
            .with_transitions([
                (0, 'a', 0, 1),
                (0, 'b', 1, 0),
                (1, 'a', 2, 0),
                (1, 'b', 0, 1),
            ])
            .into_dpa(0);
        let a = (&dpa).with_initial(1).collect_dpa();
        assert!(!Equivalence::of(&dpa).and(&a).holds());

        let cong = RightCongruence::from_pointed(dpa.prefix_congruence());
        assert_eq!(cong.state_count(), 2);
        assert_eq!(cong.initial(), cong.reached_state("aa").unwrap());
        assert!(cong.congruent("", "aa") == Some(true));
        assert!(cong.congruent("ab", "baaba") == Some(true));

        let dpa = DTS::builder()
            .with_transitions([
                (0, 'a', 0, 0),
                (0, 'b', 0, 1),
                (1, 'a', 0, 0),
                (1, 'b', 0, 0),
            ])
            .into_dpa(0);
        let cong = dpa.prefix_congruence();
        assert_eq!(cong.state_count(), 1);
    }

    #[test]
    fn bug_normalized() {
        let dpa = Builder::without_state_colors()
            .with_transitions([
                (0, 'a', 3, 2),
                (0, 'b', 3, 0),
                (1, 'a', 4, 0),
                (1, 'b', 3, 2),
                (2, 'a', 2, 1),
                (2, 'b', 0, 2),
            ])
            .into_dpa(0);

        let normalized = dpa.normalized();
        assert_eq!(normalized.run("aaa").last_edge_color(), Some(0));
        assert_eq!(normalized.run("aa").last_edge_color(), Some(0));
        assert_eq!(normalized.run("aab").last_edge_color(), Some(0));
    }

    #[test]
    fn parity_variants_and_word_types() {
        use crate::automaton::{
            MaxEvenParityCondition, MaxOddParityCondition, MinOddParityCondition,
        };
        use crate::ts::Builder;

        // 'a' loops with priority 1, 'b' goes to a state looping with priority 2 on both symbols
        let ts = Builder::without_state_colors()
            .with_edges([
                (0, 'a', 1, 0),
                (0, 'b', 2, 1),
                (1, 'a', 2, 1),
                (1, 'b', 2, 1),
            ])
            .into_dts_with_initial(0);
        let (ts, initial) = ts.decompose();
        let min_even: DPA<_> = DPA::from_parts(ts.clone(), initial);
        let max_even: DPA<_, MaxEvenParityCondition> = DPA::from_parts(ts.clone(), initial);
        let min_odd: DPA<_, MinOddParityCondition> = DPA::from_parts(ts.clone(), initial);
        let max_odd: DPA<_, MaxOddParityCondition> = DPA::from_parts(ts, initial);

        // a^ω: only priority 1 recurs
        let a = upw!("a");
        assert!(!min_even.accepts(&a) && !max_even.accepts(&a));
        assert!(min_odd.accepts(&a) && max_odd.accepts(&a));
        // b^ω: only priority 2 recurs
        let b = upw!("b");
        assert!(min_even.accepts(&b) && max_even.accepts(&b));
        assert!(!min_odd.accepts(&b) && !max_odd.accepts(&b));
    }
}
