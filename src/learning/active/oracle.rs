// use std::cell::RefCell;

use crate::alphabet::Alphabet;
use crate::automaton::{DFA, MealyLike, MealyMachine, MooreMachine};
use crate::learning::passive::SetSample;
use crate::representation::CollectPointed;
use crate::ts::Deterministic;
use crate::ts::operations::Product;
use crate::word::{FiniteWord, Word};
use crate::{Color, DTS, Int, Lattice, Pointed, States, TransitionSystem, Void};
// use crate::math::FxIndexSet;

use super::Hypothesis;
use crate::learning::LearningError;

/// A counterexample to a hypothesis: a word together with the output that the oracle expects for it.
pub type Counterexample<A, O> = (Vec<<A as Alphabet>::Symbol>, O);

/// A trait that encapsulates a minimally adequate teacher (MAT) for active learning. This is mainly used by
/// L*-esque algorithms and can be implemented by wildly different types, for example an automaton, a function
/// or even a collection of words.
///
/// This trait is designed in a generic way, allowing us to use it for learning a priority mapping, which assigns
/// non-empty finite words a value of type `Output`. This means we can learn a Mealy machine by using priorities as
/// the `Output` type, but it also enables us to learn a regular language/deterministic finite automaton by using
/// `bool` as the `Output` type.
pub trait Oracle {
    /// The alphabet of the language or mapping that is learned.
    type Alphabet: Alphabet;
    /// The type of outputs that the oracle produces for a word.
    type Output: Color + Eq + std::hash::Hash;
    /// Returns the alphabet of the oracle.
    fn alphabet(&self) -> &Self::Alphabet;

    /// Answers a membership query, i.e. returns the output for the given `word`.
    fn output<W: FiniteWord<Symbol = <Self::Alphabet as Alphabet>::Symbol>>(
        &self,
        word: W,
    ) -> Self::Output;

    /// Answers an equivalence query: returns `Ok` if the `hypothesis` agrees with the oracle, otherwise
    /// a [`Counterexample`].
    fn equivalence<H>(
        &self,
        hypothesis: &H,
    ) -> Result<(), Counterexample<Self::Alphabet, Self::Output>>
    where
        H: Hypothesis<Alphabet = Self::Alphabet, Output = Self::Output>;
}

/// Creates a hypothesis from the alphabet of the oracle.
///
/// This is only a stub so far, use [`LStar`](super::LStar) to learn a hypothesis.
pub fn lstar<H, O>(oracle: O) -> H
where
    O: Oracle,
    H: Hypothesis<Alphabet = O::Alphabet, Output = O::Output> + for<'a> From<&'a O::Alphabet>,
{
    oracle.alphabet().into()
}

/// An oracle/minimally adequate teacher based on a [`SetSample`]. It answers membership queries by looking up the
/// word in the sample and returning the corresponding color. If the word is not in the sample, it returns the
/// default color. Equivalence queries are perfomed by checking if the hypothesis produces the same output as the
/// sample for all words in the sample.
#[derive(Debug, Clone)]
pub struct SampleOracle<A: Alphabet, W: Word<Symbol = A::Symbol>> {
    sample: SetSample<A, W>,
    default: bool,
}

impl<A: Alphabet, X: FiniteWord<Symbol = A::Symbol>> Oracle for SampleOracle<A, X> {
    type Alphabet = A;

    type Output = bool;

    fn output<W: FiniteWord<Symbol = <Self::Alphabet as Alphabet>::Symbol>>(
        &self,
        word: W,
    ) -> Self::Output {
        // the words of the sample may have another type than `word`, so compare their symbols
        let is_in = |mut words: Box<dyn Iterator<Item = &X> + '_>| {
            words.any(|w| w.symbols().eq(word.symbols()))
        };
        if is_in(Box::new(self.sample.positive_words())) {
            true
        } else if is_in(Box::new(self.sample.negative_words())) {
            false
        } else {
            self.default
        }
    }

    fn equivalence<H>(
        &self,
        hypothesis: &H,
    ) -> Result<(), Counterexample<Self::Alphabet, Self::Output>>
    where
        H: Hypothesis<Alphabet = Self::Alphabet, Output = Self::Output>,
    {
        for (word, expected) in self.sample.entries() {
            if hypothesis.output(word) != expected {
                return Err((word.symbols().collect(), expected));
            }
        }
        Ok(())
    }

    fn alphabet(&self) -> &Self::Alphabet {
        self.sample.alphabet()
    }
}

impl<A: Alphabet, W: Word<Symbol = A::Symbol>> SampleOracle<A, W> {
    /// Returns a reference to the underlying alphabet, as provided by [`SetSample::alphabet()`].
    pub fn alphabet(&self) -> &A {
        self.sample.alphabet()
    }
}

impl<A: Alphabet, W: FiniteWord<Symbol = A::Symbol>> SampleOracle<A, W> {
    /// Creates a new instance of a [`SampleOracle`] with the given sample and default color.
    pub fn new(sample: SetSample<A, W>, default: bool) -> Self {
        Self { sample, default }
    }
}

impl<A: Alphabet, W: FiniteWord<Symbol = A::Symbol>> From<(SetSample<A, W>, bool)>
    for SampleOracle<A, W>
{
    fn from((value, default): (SetSample<A, W>, bool)) -> Self {
        Self::new(value, default)
    }
}

/// An oracle base on a [`DFA`] instance. It answers membership queries by running the word through the
/// automaton and returning the result. Equivalence queries are performed by intersecting the hypothesis with
/// the negated input automaton and returning a counterexample if the intersection is non-empty.
#[derive(Debug, Clone)]
pub struct DFAOracle<A: Alphabet> {
    automaton: DFA<DTS<A, bool, Void>>,
    //     negated: DFA<DTS<A, bool, Void>>,
}

impl<A: Alphabet> DFAOracle<A> {
    /// Creates a new instance of a [`DFAOracle`] from the given automaton.
    pub fn new(automaton: DFA<DTS<A, bool, Void>>) -> Self {
        //         let negated = automaton.negation().reachable_part().collect_dfa();
        Self { automaton }
        // Self { negated, automaton }
    }
}

impl<A: Alphabet> Oracle for DFAOracle<A> {
    type Alphabet = A;
    type Output = bool;

    fn alphabet(&self) -> &Self::Alphabet {
        self.automaton.alphabet()
    }

    fn output<W: FiniteWord<Symbol = A::Symbol>>(&self, word: W) -> bool {
        self.automaton.accepts(word)
    }

    fn equivalence<H>(
        &self,
        hypothesis: &H,
    ) -> Result<(), Counterexample<Self::Alphabet, Self::Output>>
    where
        H: Hypothesis<Alphabet = Self::Alphabet, Output = Self::Output>,
    {
        for mr in (&self.automaton)
            .ts_product(hypothesis)
            .minimal_representatives_iter()
        {
            match (self.automaton.accepts(&mr), hypothesis.output(&mr)) {
                (b, bb) if b != bb => return Err((mr.to_vec(), b)),
                _ => (),
            }
        }
        Ok(())
    }
}

/// An oracle based on a [`MealyMachine`]. It answers membership queries with the last output
/// of the machine and equivalence queries by comparing it to the hypothesis.
#[derive(Clone)]
pub struct MealyOracle<A: Alphabet, C: Color + Lattice = Int> {
    mm: MealyMachine<DTS<A, Void, C>>,
}

impl<A: Alphabet, C: Color + Lattice> MealyOracle<A, C> {
    /// Creates a new [`MealyOracle`] from something that behaves like a Mealy machine.
    ///
    /// # Errors
    /// Fails if the machine is not complete, as the oracle needs an output for every word.
    pub fn new(
        mm: impl MealyLike<Alphabet = A, EdgeColor = C> + States,
    ) -> Result<Self, LearningError> {
        let mm: MealyMachine<DTS<A, Void, C>> = mm.erase_state_colors().collect_mealy();
        if !mm.is_complete() {
            return Err(LearningError::IncompleteOracle);
        }
        Ok(Self { mm })
    }
}

impl<A: Alphabet, C: Color + Lattice + Eq + std::hash::Hash> Oracle for MealyOracle<A, C> {
    type Alphabet = A;

    type Output = C;

    fn alphabet(&self) -> &Self::Alphabet {
        self.mm.alphabet()
    }

    fn output<W: FiniteWord<Symbol = <Self::Alphabet as Alphabet>::Symbol>>(
        &self,
        word: W,
    ) -> Self::Output {
        // the machine is complete, so only the empty word has no output
        self.mm.transform(&word).unwrap_or_else(|| {
            tracing::warn!("the Mealy oracle was asked for the output of the empty word");
            C::bottom()
        })
    }

    fn equivalence<H>(
        &self,
        hypothesis: &H,
    ) -> Result<(), Counterexample<Self::Alphabet, Self::Output>>
    where
        H: Hypothesis<Alphabet = Self::Alphabet, Output = Self::Output>,
    {
        for mtr in (&self.mm)
            .ts_product(hypothesis)
            .minimal_transition_representatives()
        {
            let expected = self.output(&mtr);
            if expected != hypothesis.output(&mtr) {
                return Err((mtr.to_vec(), expected));
            }
        }
        Ok(())
    }
}

/// An oracle based on a [`MealyMachine`], which additionally stores a default color that
/// is returned if the word does not produce a color in the automaton.
#[derive(Clone)]
pub struct CompletingMealyOracle<A: Alphabet, C: Color = Int> {
    automaton: MealyMachine<DTS<A, Void, C>>,
    default: C,
    //     missed: RefCell<FxIndexSet<Vec<A::Symbol>>>,
}

impl<A: Alphabet, C: Color> CompletingMealyOracle<A, C> {
    /// Creates a new [`MealyOracle`] based on an instance of [`MealyMachine`].
    pub fn new(
        automaton: impl Deterministic<Alphabet = A, EdgeColor = C> + Pointed + States,
        default: C,
    ) -> Self {
        Self {
            automaton: automaton.erase_state_colors().collect_mealy(),
            default,
            //             missed: RefCell::new(FxIndexSet::default()),
        }
    }
    /// Returns the alphabet of the underlying machine.
    pub fn alphabet(&self) -> &A {
        self.automaton.alphabet()
    }
}

impl<A: Alphabet, C: Color + Eq + std::hash::Hash + Ord> Oracle for CompletingMealyOracle<A, C> {
    type Alphabet = A;
    type Output = C;

    fn output<W: FiniteWord<Symbol = A::Symbol>>(&self, word: W) -> C {
        self.automaton
            .run(word)
            .last_edge_color()
            .unwrap_or(self.default.clone())
    }

    fn equivalence<H>(
        &self,
        hypothesis: &H,
    ) -> Result<(), Counterexample<Self::Alphabet, Self::Output>>
    where
        H: Hypothesis<Alphabet = Self::Alphabet, Output = Self::Output>,
    {
        for mr in (&self.automaton)
            .ts_product(hypothesis)
            .minimal_transition_representatives()
        {
            let Some(expected) = self.automaton.transform(&mr) else {
                continue;
            };
            // .unwrap_or_else(|| {
            //     let Some(default) = &self.default else {
            //         panic!("Oracle must be total or provide a default!")
            //     };
            // self.missed.borrow_mut().insert(mr.clone());
            // trace!("returning default for {mr:?}");
            // default.clone()
            // });
            let output = hypothesis.output(&mr);
            if output != expected {
                return Err((mr.to_vec(), expected));
            }
        }
        Ok(())
    }

    fn alphabet(&self) -> &A {
        self.automaton.alphabet()
    }
}

/// An oracle based on a `MooreMachine`.
#[derive(Debug, Clone)]
pub struct MooreOracle<D> {
    automaton: D,
}

impl<D: Deterministic + States> Oracle for MooreOracle<MooreMachine<D>>
where
    D::StateColor: Color + Default + Ord + Eq + std::hash::Hash,
{
    type Alphabet = D::Alphabet;
    type Output = D::StateColor;

    fn alphabet(&self) -> &Self::Alphabet {
        self.automaton.alphabet()
    }

    fn output<W: FiniteWord<Symbol = <Self::Alphabet as Alphabet>::Symbol>>(
        &self,
        word: W,
    ) -> Self::Output {
        self.automaton
            .map(word)
            .expect("underlying transition system of Moore oracle must be complete")
    }

    fn equivalence<H>(
        &self,
        hypothesis: &H,
    ) -> Result<(), Counterexample<Self::Alphabet, Self::Output>>
    where
        H: Hypothesis<Alphabet = Self::Alphabet, Output = Self::Output>,
    {
        for mr in (&self.automaton)
            .ts_product(hypothesis)
            .minimal_representatives_iter()
        {
            match (
                self.automaton
                    .map(&mr)
                    .expect("source automaton must be complete"),
                hypothesis.output(&mr),
            ) {
                (c, cc) if c != cc => return Err((mr.to_vec(), c)),
                _ => (),
            }
        }
        Ok(())
    }
}

impl<D: Deterministic + States> MooreOracle<MooreMachine<D>> {
    /// Creates a new [`MooreOracle`] based on a `MooreMachine`.
    ///
    /// # Errors
    /// Fails if the machine is not complete, as the oracle needs an output for every word.
    pub fn new(automaton: MooreMachine<D>) -> Result<Self, LearningError> {
        if !automaton.is_complete() {
            return Err(LearningError::IncompleteOracle);
        }
        Ok(Self { automaton })
    }
}

#[cfg(test)]
mod tests {
    use crate::automaton::MealyMachine;
    use crate::{DTS, States};

    use crate::learning::active::LStar;

    use super::CompletingMealyOracle;

    #[test]
    fn mealy_al() {
        let target = DTS::builder()
            .with_transitions([
                (0, 'a', 1, 1),
                (0, 'b', 1, 0),
                (0, 'c', 1, 0),
                (1, 'a', 0, 0),
                (1, 'b', 1, 0),
                (1, 'c', 1, 0),
                (2, 'a', 3, 0),
                (2, 'b', 0, 1),
                (2, 'c', 1, 0),
            ])
            .into_mealy(0);
        let oracle = CompletingMealyOracle::new(target, 0);
        let alphabet = oracle.alphabet().clone();
        let mut learner = LStar::new(alphabet, oracle);
        let mm: MealyMachine = learner.infer().unwrap();
        assert_eq!(mm.state_count(), 2);
    }
}
