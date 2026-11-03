use std::borrow::Cow;
use std::collections::VecDeque;
use std::fmt::Debug;

use crate::alphabet::Alphabet;
use crate::automaton::{DFA, DPA};
use crate::families::FWPM;
use crate::learning::{LearningError, WeakPriorityMapping};
use crate::math::{FxIndexMap, FxIndexSet};
use crate::representation::CollectPointed;
use crate::ts::{
    DenseId, Deterministic, DeterministicEdgesFrom, EdgeOf, EdgeRef, ForAlphabet, IdType,
    Sproutable, StateId, SymbolOf,
};
use crate::{DTS, Int, Pointed, RightCongruence, States, TransitionSystem, Void};
use itertools::Itertools;
use tracing::debug;

type Dfa<A> = DFA<DTS<A, bool, Void>>;

/// The maximal number of priorities that [`build_precise_dpa_for`] supports.
const MAX_PRIORITIES: usize = 8;

/// Builds the minimized precise DPA for the given [`FWPM`]. The size of the arrays in the states of
/// the intermediate [`PreciseDPA`] is chosen according to the complexity of the family.
///
/// # Errors
/// Fails if the family uses no priority or more than 8 priorities.
pub fn build_precise_dpa_for<A: Alphabet>(
    fwpm: FWPM<A>,
) -> Result<DPA<DTS<A, Void, Int>>, LearningError> {
    let dpa = match fwpm.complexity() {
        0 => {
            return Err(LearningError::Priorities {
                used: 0,
                max: MAX_PRIORITIES,
            });
        }
        1 => PreciseDPA::<A, 1>::try_from(fwpm)?
            .reachable_part()
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        2 => PreciseDPA::<A, 2>::try_from(fwpm)?
            .reachable_part()
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        3 => PreciseDPA::<A, 3>::try_from(fwpm)?
            .reachable_part()
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        4 => PreciseDPA::<A, 4>::try_from(fwpm)?
            .reachable_part()
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        5 => PreciseDPA::<A, 5>::try_from(fwpm)?
            .reachable_part()
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        6 => PreciseDPA::<A, 6>::try_from(fwpm)?
            .reachable_part()
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        7 => PreciseDPA::<A, 7>::try_from(fwpm)?
            .reachable_part()
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        8 => PreciseDPA::<A, 8>::try_from(fwpm)?
            .reachable_part()
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        used => {
            return Err(LearningError::Priorities {
                used,
                max: MAX_PRIORITIES,
            });
        }
    };
    Ok(dpa)
}

type ClassId = StateId;

/// We use const generics in the definition of the precise DPA. Therefore, it is necessary to bound the
/// number of colors that can be used. This constant is used as such a bound.
pub const PRECISE_DPA_COLORS: usize = 5;

/// A PState is a state in the precise DPA. It keeps track of the class in the leading
/// congruence and for each Mostowski level, it tracks the class and the state in the
/// corresponding progress DFA. We use const generics (the parameter `N`) to ensure that
/// `PState`s are [`Copy`].
#[derive(Copy, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PState<const N: usize> {
    class: StateId,
    progress_classes: [StateId; N],
    progress_states: [StateId; N],
}

impl<const N: usize> IdType for PState<N> {}

impl<const N: usize> std::fmt::Display for PState<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{} | {}]",
            self.class,
            self.progress_classes()
                .zip(self.progress_states())
                .map(|(c, q)| format!("({c} - {q})"))
                .join(", ")
        )
    }
}

impl<const N: usize> PState<N> {
    /// Returns the index of the class in the leading congruence.
    pub fn class(&self) -> ClassId {
        self.class
    }

    /// Returns an iterator over the classes of the currently active DFAs.
    pub fn progress_classes(&self) -> impl Iterator<Item = ClassId> + '_ {
        self.progress_classes.iter().cloned()
    }

    /// Returns an iterator over the states of the currently active DFAs.
    pub fn progress_states(&self) -> impl Iterator<Item = StateId> + '_ {
        self.progress_states.iter().cloned()
    }

    /// Creates a new instance of `Self` from the index of the class in the leading
    /// congruence and iterators over the classes and states of the currently active
    /// DFAs.
    pub fn from_iters<I: IntoIterator<Item = ClassId>, J: IntoIterator<Item = StateId>>(
        leading: ClassId,
        pc: I,
        pq: J,
    ) -> Self {
        let mut c = [StateId::default(); N];
        let mut q = [StateId::default(); N];
        pc.into_iter().enumerate().for_each(|(i, o)| c[i] = o);
        pq.into_iter().enumerate().for_each(|(i, o)| q[i] = o);
        Self {
            class: leading,
            progress_classes: c,
            progress_states: q,
        }
    }

    /// Creates a new instance of `Self` from the index of the class in the leading
    /// congruence and arrays of the classes and states of the currently active DFAs.
    pub fn new(leading: ClassId, pc: &[ClassId], pq: &[StateId]) -> Self {
        let c = std::array::from_fn(|i| pc[i]);
        let p = std::array::from_fn(|i| pq[i]);

        Self {
            class: leading,
            progress_classes: c,
            progress_states: p,
        }
    }
}

/// The precise DPA is a construction for going from a specifically colored FORC to a deterministic
/// parity automaton. It is described <https://arxiv.org/pdf/2302.11043.pdf>[here, below Lemma 15].
/// A precise DPA is built from a [`FWPM`] with `PreciseDPA::from`. It is an implicit system, so
/// call `reachable_part` before collecting it, as [`infer_precise_dpa`](super::infer_precise_dpa) shows.
#[derive(Clone)]
pub struct PreciseDPA<A: Alphabet, const N: usize = 8> {
    states: Vec<PState<N>>,
    cong: RightCongruence<DTS<A>>,
    expressions: std::collections::BTreeMap<A::Symbol, A::Expression>,
    /// Nat -> class -> DFA
    dfas: Vec<[Dfa<A>; N]>,
}

impl<A: Alphabet, const N: usize> TransitionSystem for PreciseDPA<A, N> {
    type StateIndex = PState<N>;

    type StateColor = Void;

    type EdgeColor = Int;

    type EdgesFromIter<'this>
        = DeterministicEdgesFrom<'this, Self>
    where
        Self: 'this;

    type Alphabet = A;

    fn alphabet(&self) -> &Self::Alphabet {
        self.cong.alphabet()
    }

    fn state_color(&self, _state: PState<N>) -> Option<Cow<'_, Void>> {
        Some(Cow::Owned(Void))
    }

    fn edges_from(&self, state: PState<N>) -> Option<Self::EdgesFromIter<'_>> {
        Some(DeterministicEdgesFrom::new(self, state))
    }
}

impl<A: Alphabet, const N: usize> Deterministic for PreciseDPA<A, N> {
    fn edge(&self, state: PState<N>, symbol: SymbolOf<Self>) -> Option<EdgeOf<'_, Self>> {
        let (i, p) = self.take_precise_transition(&state, symbol)?;
        Some(EdgeRef::owned(state, self.expressions.get(&symbol)?, i, p))
    }
}

impl<A: Alphabet, const N: usize> Pointed for PreciseDPA<A, N> {
    fn initial(&self) -> Self::StateIndex {
        *self.states.first().expect("We add this during creation")
    }
}

impl<A: Alphabet, const N: usize> PreciseDPA<A, N> {
    /// Creates a new precise DPA from the given leading congruence and, for each of its classes, the
    /// `N` DFAs of the priority levels.
    ///
    /// # Errors
    /// Fails if there is not exactly one array of DFAs for each class of the congruence.
    pub fn new(
        cong: RightCongruence<DTS<A>>,
        dfas: Vec<[Dfa<A>; N]>,
    ) -> Result<Self, LearningError> {
        if dfas.len() != cong.state_count() {
            return Err(LearningError::Incomplete);
        }
        let e = cong.initial();
        let levels = dfas.get(e.into_usize()).ok_or(LearningError::Incomplete)?;
        let initial = PState::from_iters(e, [e; N], levels.iter().map(|dfa| dfa.initial()));
        Ok(Self {
            states: vec![initial],
            expressions: cong.alphabet().expression_map(),
            cong,
            dfas,
        })
    }

    /// Returns the DFAs of the given priority level, one for each class of the leading congruence.
    pub fn dfas_level(&self, level: usize) -> impl Iterator<Item = (usize, &'_ Dfa<A>)> + '_ {
        self.dfas.iter().map(move |dfa| &dfa[level]).enumerate()
    }

    /// Returns a reference to the leading congruence.
    pub fn cong(&self) -> &RightCongruence<DTS<A>> {
        &self.cong
    }

    /// Given a [`PState`], returns an iterator over the DFAs that are currently active.
    pub fn dfas<'a>(&'a self, q: &'a PState<N>) -> impl Iterator<Item = &'a Dfa<A>> + 'a {
        q.progress_classes()
            .enumerate()
            .map(move |(i, c)| &self.dfas[c.into_usize()][i])
    }

    /// Given a [`PState`] and a symbol, returns the index of the least accepting DFA (which is
    /// the priority of the corresponding edge) and the successor [`PState`]. Returns `None` if the
    /// leading congruence or one of the DFAs is not complete or if no DFA is accepting (the last
    /// one always is for a family of weak priority mappings).
    pub fn take_precise_transition(&self, q: &PState<N>, a: A::Symbol) -> Option<(Int, PState<N>)> {
        let d = self.cong().successor(q.class(), a)?;

        let progress = self
            .dfas(q)
            .zip(q.progress_classes())
            .zip(q.progress_states())
            .map(|((dfa, c), q)| {
                let p = dfa.successor(q, a)?;
                let b = *dfa.state_color(p)?;
                Some((c, p, b))
            })
            .collect::<Option<Vec<_>>>()?;

        let least_accepting = progress.iter().position(|(_, _, b)| *b)?;

        let reached_pstate = PState::from_iters(
            d,
            progress
                .iter()
                .enumerate()
                .map(|(i, (c, _p, _b))| if i < least_accepting { *c } else { d }),
            progress.iter().enumerate().map(|(i, (_c, p, _b))| {
                if i < least_accepting {
                    *p
                } else {
                    self.dfas[d.into_usize()][i].initial()
                }
            }),
        );

        Some((Int::try_from(least_accepting).ok()?, reached_pstate))
    }
}

impl<A: Alphabet, const N: usize> Debug for PreciseDPA<A, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreciseDPA")
            .field("classes", &self.cong.state_count())
            .field("priorities", &N)
            .finish()
    }
}

fn padding_universal_dfa<A: Alphabet>(alphabet: &A) -> Dfa<A> {
    let mut ts = DTS::for_alphabet_size_hint(alphabet.clone(), 1);
    let e = ts.add_state(true);

    for sym in alphabet.universe() {
        ts.add_edge((e, alphabet.make_expression(sym), Void, e));
    }
    DFA::from_parts(ts, e)
}

/// Decomposes a weak priority mapping into a sequence of DFAs, where the i-th DFA accepts all
/// non-empty words which are mapped to the i-th smallest priority or less. As the priority of a
/// word is the color of the last edge, the states of the DFAs remember the color of the edge
/// through which they were entered; the initial state has no such color (it is accepting, but
/// can only be reached by the empty word).
fn priority_dfas<A: Alphabet>(pm: &WeakPriorityMapping<A>) -> Vec<Dfa<A>> {
    let priorities = pm.color_range().collect::<FxIndexSet<_>>();
    priorities
        .into_iter()
        .sorted()
        .map(|threshold| {
            let mut ts = DTS::for_alphabet(pm.alphabet().clone());
            let mut ids = FxIndexMap::default();
            let initial = ts.add_state(true);
            ids.insert((pm.initial(), None), initial);
            let mut queue = VecDeque::from([(pm.initial(), initial)]);
            while let Some((q, source)) = queue.pop_front() {
                for edge in pm.edges_from(q).into_iter().flatten() {
                    let key = (edge.target(), Some(*edge.color()));
                    let target = *ids.entry(key).or_insert_with(|| {
                        let id = ts.add_state(*edge.color() <= threshold);
                        queue.push_back((key.0, id));
                        id
                    });
                    ts.add_edge((source, edge.expression().clone(), Void, target));
                }
            }
            DFA::from_parts(ts, initial).minimize()
        })
        .collect()
}

impl<A: Alphabet, const N: usize> TryFrom<FWPM<A>> for PreciseDPA<A, N> {
    type Error = LearningError;

    fn try_from(value: FWPM<A>) -> Result<Self, LearningError> {
        let start = std::time::Instant::now();

        let leading = value.leading().clone();
        let padding_dfa = padding_universal_dfa(leading.alphabet());
        let mut prc_dfas = Vec::with_capacity(leading.state_count());
        let mut pms = value.iter().collect_vec();
        pms.sort_by_key(|(idx, _)| *idx);
        for (idx, mm) in pms {
            let mut dfas = priority_dfas(mm);
            if dfas.len() > N {
                return Err(LearningError::Priorities {
                    used: dfas.len(),
                    max: N,
                });
            }
            dfas.resize(N, padding_dfa.clone());
            let array_dfas = dfas.try_into().map_err(|_| LearningError::Incomplete)?;
            // the classes must be numbered consecutively, otherwise a class has no mapping
            if idx.into_usize() != prc_dfas.len() {
                return Err(LearningError::Incomplete);
            }
            prc_dfas.push(array_dfas);
        }

        debug!(
            "Building precise DPA with {N} priorities took {} microseconds",
            start.elapsed().as_micros()
        );

        PreciseDPA::new(leading, prc_dfas)
    }
}

#[cfg(test)]
mod tests {
    use crate::Void;
    use crate::alphabet::CharAlphabet;
    use crate::{DTS, TransitionSystem};

    use super::PreciseDPA;

    #[test]
    fn precise_dpa() {
        let _alph = CharAlphabet::of_size(3);

        let cong = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 1),
                (0, 'b', Void, 0),
                (0, 'c', Void, 0),
                (1, 'a', Void, 0),
                (1, 'b', Void, 1),
                (1, 'c', Void, 1),
            ])
            .default_color(Void)
            .into_right_congruence(0);

        let de0 = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 0),
                (0, 'b', Void, 1),
                (0, 'c', Void, 0),
                (1, 'a', Void, 1),
                (1, 'b', Void, 1),
                (1, 'c', Void, 1),
            ])
            .with_state_colors([false, true])
            .into_dfa(0);
        let da0 = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 0),
                (0, 'b', Void, 0),
                (0, 'c', Void, 1),
                (1, 'a', Void, 1),
                (1, 'b', Void, 1),
                (1, 'c', Void, 1),
            ])
            .with_state_colors([false, true])
            .into_dfa(0);

        let de1 = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 0),
                (0, 'b', Void, 2),
                (0, 'c', Void, 1),
                (1, 'a', Void, 0),
                (1, 'b', Void, 2),
                (1, 'c', Void, 2),
                (2, 'a', Void, 2),
                (2, 'b', Void, 2),
                (2, 'c', Void, 2),
            ])
            .with_state_colors([false, false, true])
            .into_dfa(0);

        let full = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 1),
                (0, 'b', Void, 1),
                (0, 'c', Void, 1),
                (1, 'a', Void, 1),
                (1, 'b', Void, 1),
                (1, 'c', Void, 1),
            ])
            .with_state_colors([false, true])
            .into_dfa(0);

        let dfas_e = [de0, de1, full.clone()];
        let dfas_a = [da0, full.clone(), full];

        let dpa = PreciseDPA::new(cong, vec![dfas_e, dfas_a]).unwrap();
        assert_eq!(dpa.reachable_state_indices().count(), 8);
    }
}
