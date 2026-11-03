use std::cell::RefCell;

use crate::DTS;
use crate::alphabet::Alphabet;
use crate::math;
use crate::ts::{ForAlphabet, Sproutable, SymbolOf};
use crate::word::Concat;
use crate::word::FiniteWord;
use itertools::Itertools;
use tracing::{debug, info, trace};

use super::{Experiment, Hypothesis, oracle::Oracle};
use crate::learning::LearningError;
// use super::ObservationTable;

const ITERATION_THRESHOLD: usize = if cfg!(debug_assertions) { 50 } else { 200000 };

type Word<D> = Vec<SymbolOf<D>>;
/// The experiments (suffixes) that distinguish the rows of the observation table of [`LStar`].
pub type Experiments<D> = Vec<Experiment<SymbolOf<D>>>;

/// An implementation of the L* algorithm.
/// # Example
/// Learning a Mealy machine from an oracle that is given by the target machine.
/// ```
/// use automata::States;
/// use automata::TransitionSystem;
/// use automata::automaton::MealyMachine;
/// use automata::learning::active::{LStar, MealyOracle};
/// use automata::ts::Builder;
///
/// let target = Builder::without_state_colors()
///     .with_edges([
///         (0, 'a', 0, 0), (0, 'b', 1, 1), (0, 'c', 2, 2),
///         (1, 'a', 0, 2), (1, 'b', 1, 1), (1, 'c', 2, 2),
///         (2, 'a', 2, 2), (2, 'b', 0, 0), (2, 'c', 1, 2),
///     ])
///     .into_mealy(0);
/// let alphabet = target.alphabet().clone();
/// let oracle = MealyOracle::new(target).unwrap();
/// let learned: MealyMachine = LStar::new(alphabet, oracle).infer().unwrap();
/// assert_eq!(learned.state_count(), 3);
/// ```
pub struct LStar<D: Hypothesis, T: Oracle<Alphabet = D::Alphabet>> {
    // the alphabet of what we are learning
    alphabet: D::Alphabet,
    // a mapping containing all queries that have been posed so far, together with their output
    queries: RefCell<std::collections::BTreeMap<Word<D>, D::Output>>,
    // the minimal access words forming the base states
    base: Vec<Word<D>>,
    // all known experiments
    experiments: Vec<Experiment<SymbolOf<D>>>,
    // mapping from input word to a bitset, where the i-th entry gives the value for
    // the output of concatenating input word and i-th experiment
    table: std::collections::BTreeMap<Word<D>, Vec<D::Output>>,
    // the oracle
    oracle: T,
    //     observations: ObservationTable<SymbolOf<D>, T::Output>,
}

impl<D: Hypothesis, T: Oracle<Alphabet = D::Alphabet, Output = D::Output>> LStar<D, T> {
    /// Creates a learner for the given alphabet that asks its queries to `oracle`.
    pub fn new(alphabet: D::Alphabet, oracle: T) -> Self {
        Self {
            experiments: D::mandatory_experiments(&alphabet).into_iter().collect(),
            //             observations: ObservationTable::with_rows_and_experiments(
            //                 [],
            //                 D::mandatory_experiments(&alphabet),
            //             ),
            alphabet,
            queries: RefCell::new(std::collections::BTreeMap::default()),
            base: vec![vec![]],
            table: std::collections::BTreeMap::default(),
            oracle,
        }
    }

    fn output(&self, w: &Word<D>) -> D::Output {
        if !self.queries.borrow().contains_key(w) {
            let c = self.oracle.output(w);
            assert!(self.queries.borrow_mut().insert(w.to_owned(), c).is_none());
        }
        self.queries.borrow().get(w).unwrap().clone()
    }

    fn update_table(&mut self) {
        let mut updates = vec![];
        let experiment_count = self.experiments.len();

        for mr in self.one_letter_extensions() {
            let stored_experiment_count = self.table.get(&mr).map(|r| r.len()).unwrap_or(0);
            if stored_experiment_count < experiment_count {
                for i in stored_experiment_count..experiment_count {
                    let concat = Concat(&mr, &self.experiments[i]).collect_vec();
                    let output = self.output(&concat).clone();
                    updates.push((mr.clone(), i, output));
                }
            } else {
                assert_eq!(
                    stored_experiment_count,
                    experiment_count,
                    "Too many experiments present for {}",
                    mr.as_string()
                );
            }
        }

        for (mr, i, output) in updates {
            assert!(i < self.experiments.len());
            let row = self.table.entry(mr).or_default();
            row.push(output);
        }

        if cfg!(debug_assertions) {
            for mr in self.one_letter_extensions() {
                let Some(val) = self.table.get(&mr) else {
                    panic!("No table entry for {}", mr.as_string());
                };
                if val.len() != experiment_count {
                    panic!(
                        "Row for {} does not have enough entries, has {} of {experiment_count}",
                        mr.as_string(),
                        val.len()
                    )
                }
            }
        }

        trace!("After update the table is\n{:?}", self);
    }

    /// Runs the algorithm until the oracle accepts the hypothesis and returns it.
    ///
    /// The number of iterations is bounded by the environment variable `MAX_ITERATIONS`, which
    /// defaults to a large constant.
    ///
    /// # Errors
    /// Fails if the iteration threshold is exceeded or if the oracle returns a counterexample on
    /// which the hypothesis agrees with it.
    pub fn infer(&mut self) -> Result<D, LearningError> {
        let start = std::time::Instant::now();
        let mut iteration = 0;
        let threshold = std::env::var("MAX_ITERATIONS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(ITERATION_THRESHOLD);

        'outer: while iteration < threshold {
            self.update_table();
            iteration += 1;
            trace!("LStar iteration {iteration} with table\n{:?}", self);
            let todo = self.rows_to_promote();
            trace!(
                "Have to promote rows: {}",
                todo.iter().map(FiniteWord::as_string).join(", ")
            );

            if !todo.is_empty() {
                for r in todo {
                    self.base.push(r);
                }
                // TODO optimize this call!
                self.update_table();
                continue 'outer;
            }

            let hypothesis = self.hypothesis();

            let Err((witness, expected_color)) = self.oracle.equivalence(&hypothesis) else {
                let duration = start.elapsed().as_millis();
                info!("Execution of LStar took {duration}ms");
                return Ok(hypothesis);
            };
            if hypothesis.output(&witness) == expected_color {
                return Err(LearningError::InvalidCounterexample);
            }
            self.process_counterexample(witness, expected_color);
        }

        Err(LearningError::IterationThreshold(threshold))
    }

    fn process_counterexample(&mut self, word: Word<D>, _color: D::Output) {
        trace!("Processing counterexample {}", word.as_string());
        for i in 0..(word.len()) {
            let suffix = Experiment(word[i..].to_vec());
            assert!(!suffix.is_empty());
            if !self.experiments.contains(&suffix) {
                trace!("Adding counterexample {}", suffix.as_string());
                self.experiments.push(suffix)
            }
        }
    }

    fn state_color(&self, mr: &Word<D>) -> D::StateColor {
        D::give_state_color(
            mr,
            &self.experiments,
            self.table
                .get(mr)
                .expect("Cannot give color for non-existent word"),
        )
    }

    fn hypothesis(&self) -> D {
        let start = std::time::Instant::now();

        let mut ts: DTS<_, _, _> = DTS::for_alphabet_size_hint(self.alphabet.clone(), 1);
        let mut state_map = math::FxIndexMap::default();
        let mut observations = math::FxIndexMap::default();

        for mr in &self.base {
            let color = self.state_color(mr);
            let id = ts.add_state(color);
            state_map.insert(mr, id);

            let observed = self.table.get(mr).unwrap();
            observations.insert(observed, mr);
        }

        if cfg!(debug_assertions) {
            for obs in self.table.values() {
                if !observations.contains_key(&obs) {
                    let to_promote = self.rows_to_promote();
                    panic!(
                        "rows {to_promote:?} are not closed even though they should be!\n{self:?}"
                    );
                }
            }
        }

        for (mr, i) in &state_map {
            for a in self.alphabet.universe() {
                let obs = self
                    .table
                    .get(&Concat(mr, [a]).into_vec())
                    .expect("Can only work if table is closed!");

                let Some(target) = observations.get(obs) else {
                    panic!(
                        "could not find target for {:?} ({mr:?} on symbol {a:?}) in table\n{:?}\n{:?}",
                        Concat(mr, [a]).into_vec(),
                        self,
                        self.table
                    );
                };

                let color = D::give_transition_color(
                    mr,
                    a,
                    target,
                    &self.experiments,
                    self.table.get(*mr).unwrap(),
                    self.table.get(*target).unwrap(),
                );

                ts.add_edge((
                    *i,
                    self.alphabet.make_expression(a),
                    color,
                    *state_map.get(target).unwrap(),
                ));
            }
        }

        let duration = start.elapsed().as_micros();
        debug!("Building hypothesis took {duration} microseconds");

        D::from_transition_system(ts, *state_map.get(&vec![]).unwrap())
    }

    //     fn inconsistent_words(&self) -> Option<Word<D>> {
    //         for (i, left) in self.base.iter().enumerate() {
    //             'middle: for right in &self.base[i..] {
    //                 if self.table.get(left) != self.table.get(right) {
    //                     continue 'middle;
    //                 }

    //                 for sym in self.alphabet.universe() {
    //                     let left_ext = left
    //                         .iter()
    //                         .chain(std::iter::once(&sym))
    //                         .cloned()
    //                         .collect_vec();
    //                     let right_ext = right
    //                         .iter()
    //                         .chain(std::iter::once(&sym))
    //                         .cloned()
    //                         .collect_vec();

    //                     let l = self.table.get(&left_ext).expect("Should be present!");
    //                     let r = self.table.get(&right_ext).expect("Should be present!");

    //                     if l == r {
    //                         continue 'middle;
    //                     }
    //                     'inner: for (j, e) in self.experiments.iter().enumerate() {
    //                         assert!(j < std::cmp::min(l.len(), r.len()));
    //                         if l[j] == r[j] {
    //                             continue 'inner;
    //                         }
    //                         return Some(Concat(vec![sym], e).into_vec());
    //                     }
    //                 }
    //             }
    //         }
    //         None
    //     }

    fn one_letter_extensions(&self) -> impl Iterator<Item = Word<D>> + '_ {
        self.base
            .iter()
            .flat_map(|w| {
                std::iter::once(w.clone()).chain(self.alphabet.universe().filter_map(|a| {
                    let mut x = w.clone();
                    x.push(a);
                    if !self.base.contains(&x) {
                        Some(x)
                    } else {
                        None
                    }
                }))
            })
            .unique()
    }

    fn rows_to_promote(&self) -> math::FxIndexSet<Word<D>> {
        trace!("deciding which rows to promote: {:?}", self);
        let start = std::time::Instant::now();

        let mut known = math::FxIndexSet::from_iter(self.base.iter().map(|b| {
            self.table
                .get(b)
                .unwrap_or_else(|| panic!("Experiment {} must be present", b.as_string()))
        }));
        trace!("start promotion search with known rows: {known:?}");
        let mut out = math::FxIndexSet::default();

        for (word, seq) in self.table.iter() {
            if known.insert(seq) {
                out.insert(word.clone());
            }
        }

        debug!(
            "Finding rows to promote took {} microseconds",
            start.elapsed().as_micros()
        );
        out
    }
}

impl<D: Hypothesis, T: Oracle<Alphabet = D::Alphabet>> std::fmt::Debug for LStar<D, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MR")?;
        for e in &self.experiments {
            write!(f, "\t{}", e.as_string())?;
        }
        for (mr, out) in &self.table {
            // base words are marked with a star
            let mark = if self.base.contains(mr) { "*" } else { "" };
            write!(f, "\n{}{}", mr.as_string(), mark)?;
            for e in out {
                write!(f, "\t{:?}", e)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::States;
    use crate::alphabet::CharAlphabet;
    use crate::automaton::Equivalence;
    use crate::automaton::{MealyMachine, MooreMachine};
    use crate::learning::active::{DFAOracle, MealyOracle, MooreOracle, Oracle};
    use crate::representation::CollectPointed;
    use crate::{DTS, Void};
    #[cfg(feature = "random")]
    use rand::RngExt;
    use tracing::trace;

    proptest::proptest! {
        #[test]
        fn lstar_learns_equivalent_dfa(target in crate::learning::properties::dfa()) {
            let oracle = DFAOracle::new(target.clone());
            let learned: MooreMachine<DTS<CharAlphabet, bool, Void>> =
                super::LStar::new(CharAlphabet::of_size(2), oracle).infer().unwrap();
            let learned = learned.collect_dfa();
            proptest::prop_assert!(Equivalence::of(&target).and(&learned).holds());
        }
    }

    #[cfg(feature = "random")]
    #[test]
    fn lstar_random_mealy() {
        let mut rng = rand::rng();
        for _i in 0..200 {
            let symbols = rng.random_range(1..5);
            let max_color = rng.random_range(1..10);
            let size = rng.random_range(1..25);

            let pre_gen = std::time::Instant::now();
            let ts = crate::random::generate_random_mealy(symbols, max_color, size);
            trace!(
                "generated mealy for size {size}, symbols {symbols} and max_color {max_color} in {} microseconds",
                pre_gen.elapsed().as_micros()
            );

            let oracle = MealyOracle::new(&ts).unwrap();

            let start = std::time::Instant::now();
            let mm: MealyMachine = super::LStar::new(oracle.alphabet().clone(), oracle)
                .infer()
                .unwrap();
            let duration = start.elapsed().as_millis();
            trace!("learning took {} ms", duration);

            if mm.state_count() != ts.state_count() {
                panic!(
                    "Sizes don't match, expected {} got {}",
                    ts.state_count(),
                    mm.state_count()
                );
            }
        }
    }
    #[cfg(feature = "random")]
    #[test]
    fn lstar_random_moore() {
        let mut rng = rand::rng();
        for _i in 0..200 {
            let symbols = rng.random_range(1..5);
            let max_color = rng.random_range(1..10);
            let size = rng.random_range(1..25);

            let pre_gen = std::time::Instant::now();
            let ts = crate::random::generate_random_moore(symbols, max_color, size);
            trace!(
                "generated Moore for size {size}, symbols {symbols} and max_color {max_color} in {} microseconds",
                pre_gen.elapsed().as_micros()
            );

            let oracle = MooreOracle::new(ts.clone()).unwrap();

            let start = std::time::Instant::now();
            let mm: MooreMachine = super::LStar::new(CharAlphabet::of_size(symbols), oracle)
                .infer()
                .unwrap();
            let duration = start.elapsed().as_millis();
            trace!("learning took {} ms", duration);

            if mm.state_count() != ts.state_count() {
                panic!(
                    "Sizes don't match, expected {} got {}",
                    ts.state_count(),
                    mm.state_count()
                );
            }
        }
    }
}
