use crate::DTS;
use crate::alphabet::Alphabet;
use crate::learning::LearningError;
use crate::learning::passive::dpainf::{dpainf, iteration_consistency_conflicts};
use crate::math;
use crate::ts::{Deterministic, StateId};
use crate::{Class, RightCongruence, families::FORC};

use super::{OmegaSample, SetSample};

/// An [`OmegaSample`] restricted/split onto one [`Class`] of a [`RightCongruence`].
#[derive(Clone)]
pub struct ClassOmegaSample<'a, A: Alphabet> {
    // placeholder: keeps the lifetime of the congruence, not read yet
    #[allow(dead_code)]
    congruence: &'a RightCongruence<DTS<A>>,
    class: Class<A::Symbol>,
    sample: OmegaSample<A>,
}

impl<A: Alphabet> std::ops::Deref for ClassOmegaSample<'_, A> {
    type Target = OmegaSample<A>;

    fn deref(&self) -> &Self::Target {
        &self.sample
    }
}

impl<A: Alphabet> std::ops::DerefMut for ClassOmegaSample<'_, A> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.sample
    }
}

impl<'a, A: Alphabet> ClassOmegaSample<'a, A> {
    /// Creates a new [`ClassOmegaSample`] from a [`RightCongruence`], a [`Class`] and a [`SetSample`].
    pub fn new(
        congruence: &'a RightCongruence<DTS<A>>,
        class: Class<A::Symbol>,
        sample: OmegaSample<A>,
    ) -> Self {
        Self {
            congruence,
            class,
            sample,
        }
    }

    /// Returns a reference to the underlying sample.
    pub fn sample(&self) -> &OmegaSample<A> {
        &self.sample
    }

    /// Gives a mutable reference to the underlying sample.
    pub fn sample_mut(&mut self) -> &mut OmegaSample<A> {
        &mut self.sample
    }

    /// Creates an empty [`ClassOmegaSample`] from a [`RightCongruence`], a [`Class`] and an alphabet.
    pub fn empty(
        congruence: &'a RightCongruence<DTS<A>>,
        class: Class<A::Symbol>,
        alphabet: A,
    ) -> Self {
        Self {
            congruence,
            class,
            sample: SetSample {
                alphabet,
                positive: math::FxIndexSet::default(),
                negative: math::FxIndexSet::default(),
            },
        }
    }
}

/// Represents a right congruence relation together with a collection of split samples, one
/// associated with each class of the congruence.
#[derive(Clone)]
pub struct SplitOmegaSample<'a, A: Alphabet> {
    congruence: &'a RightCongruence<DTS<A>>,
    split: std::collections::BTreeMap<StateId, ClassOmegaSample<'a, A>>,
}

impl<'a, A: Alphabet> SplitOmegaSample<'a, A> {
    /// Creates a new object from the given congruence and the split
    pub fn new(
        congruence: &'a RightCongruence<DTS<A>>,
        split: std::collections::BTreeMap<StateId, ClassOmegaSample<'a, A>>,
    ) -> Self {
        Self { congruence, split }
    }

    /// Obtain a reference to the split sample for the given class/index.
    pub fn get(&self, index: StateId) -> Option<&ClassOmegaSample<'a, A>> {
        self.split.get(&index)
    }

    /// Obtains an iterator over all classes in the split sample.
    pub fn classes(&self) -> impl Iterator<Item = &'_ Class<A::Symbol>> + '_ {
        self.split.values().map(|sample| &sample.class)
    }

    /// Returns a reference to the underlying congruence.
    pub fn cong(&self) -> &'a RightCongruence<DTS<A>> {
        self.congruence
    }
}

impl<A: Alphabet> SplitOmegaSample<'_, A> {
    /// Infers a family of right congruences by first constructing a conflict relation which is then used
    /// as a constraint for the sprout/glerc algorithm.
    ///
    /// # Errors
    /// Fails if the sprout algorithm exceeds its threshold, which means that the sample is not
    /// consistent.
    pub fn infer_forc(&self) -> Result<FORC<A>, LearningError> {
        let mut progress = Vec::new();
        for class in self.classes() {
            let conflicts = iteration_consistency_conflicts(self, class.clone())?;
            let state = self
                .cong()
                .reached_state(class)
                .ok_or(LearningError::Incomplete)?;
            // SeparatesIdempotents::new(split_sample.get(&c).expect("This must exist")),
            progress.push((state, dpainf(conflicts, vec![], false, None)?));
        }
        // sort by class to be independent of the iteration order of the split
        progress.sort_by_key(|(state, _)| *state);
        Ok(FORC::from_iter(self.cong().clone(), progress))
    }
}
