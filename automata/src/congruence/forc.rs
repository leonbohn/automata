use crate::prelude::*;

/// A family of right congruences (FORC) consists of a *leading* right congruence and for each
/// class of this congruence a *progress* right congruence.
#[derive(Clone)]
pub struct FORC<A: Alphabet, Q: Color = Void, C: Color = Void> {
    pub(crate) leading: RightCongruence<A>,
    pub(crate) progress: math::OrderedMap<DefaultIdType, RightCongruence<A, Q, C>>,
}

impl<A: Alphabet, Q: Color, C: Color> FORC<A, Q, C> {
    /// Creates a new FORC with the given leading congruence and progress congruences.
    pub fn new(
        leading: RightCongruence<A>,
        progress: math::OrderedMap<DefaultIdType, RightCongruence<A, Q, C>>,
    ) -> Self {
        Self { leading, progress }
    }

    /// Returns a reference to the leading right congruence.
    pub fn leading(&self) -> &RightCongruence<A> {
        &self.leading
    }

    /// Insert a new progress congruence for the given class.
    pub fn insert(
        &mut self,
        class: StateIndex<RightCongruence<A>>,
        congruence: RightCongruence<A, Q, C>,
    ) {
        self.progress.insert(class, congruence);
    }

    /// Tries to obtain a reference to the progress right congruence for the given `class`.
    pub fn prc(&self, class: StateIndex<RightCongruence<A>>) -> Option<&RightCongruence<A, Q, C>> {
        self.progress.get(&class)
    }

    /// Returns an iterator over the progress congruences.
    pub fn prc_iter(
        &self,
    ) -> impl Iterator<Item = (&'_ DefaultIdType, &'_ RightCongruence<A, Q, C>)> + '_ {
        self.progress.iter()
    }

    /// Creates a new FORC from the given leading congruence and progress congruences.
    pub fn from_iter<I: IntoIterator<Item = (DefaultIdType, RightCongruence<A, Q, C>)>>(
        leading: RightCongruence<A>,
        progress: I,
    ) -> Self {
        Self {
            leading,
            progress: progress.into_iter().collect(),
        }
    }
}

impl<A: Alphabet + PartialEq, Q: Color + Eq, C: Color + Eq> PartialEq for FORC<A, Q, C> {
    fn eq(&self, _other: &Self) -> bool {
        todo!()
    }
}

impl<A: Alphabet + PartialEq, Q: Color + PartialEq, C: Color + PartialEq> Eq for FORC<A, Q, C> {}

impl<A: Alphabet, Q: Color, C: Color> std::fmt::Debug for FORC<A, Q, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}\n{:?}", "leading congruence", self.leading())?;
        let names = self.leading.acceptance().ensure_from(self.leading.ts(), 0);
        for (c, rc) in self.prc_iter() {
            let class_name = names.get_by_left(c).unwrap();
            write!(f, "progress right congruence[{:?}]\n{:?}", &class_name, rc)?;
        }
        Ok(())
    }
}
