use crate::alphabet::Symbol;
use crate::math;
use crate::word::{FiniteWord, Word};
use std::hash::Hash;

/// A suffix that is used to distinguish the rows of an observation table.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Experiment<S>(pub(super) Vec<S>);

impl<S> Experiment<S> {
    /// The empty experiment.
    pub fn empty() -> Self {
        Self(vec![])
    }
    /// Returns true if the experiment consists of exactly the given `letter`.
    pub fn is_letter(&self, letter: S) -> bool
    where
        S: Symbol,
    {
        self.0 == [letter]
    }
}

impl<S: Symbol> FiniteWord for Experiment<S> {
    type Symbols<'this>
        = std::iter::Cloned<std::slice::Iter<'this, S>>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.0.iter().cloned()
    }
}

impl<S: Symbol> Word for Experiment<S> {
    type Symbol = S;
    type Kind = crate::word::Finite;
    fn nth(&self, position: usize) -> Option<S> {
        self.0.get(position).cloned()
    }
}

/// A word that labels a row of an observation table.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Representative<S>(pub(super) Vec<S>);

/// The outputs of the oracle for a row, one for each experiment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputRow<X>(pub(super) Vec<X>);

// placeholder: the table is not used by `LStar` yet
/// An observation table: for each row (representative) it stores the output of the oracle on the
/// representative followed by each experiment.
#[allow(dead_code)]
pub struct ObservationTable<S, X> {
    pub(crate) experiments: Vec<Experiment<S>>,
    pub(crate) outputs: math::FxIndexMap<Representative<S>, OutputRow<X>>,
}

impl<S, X> Default for ObservationTable<S, X>
where
    S: Hash + Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<S, X> ObservationTable<S, X>
where
    S: Hash + Eq,
{
    /// Creates an empty table.
    pub fn new() -> Self {
        Self {
            experiments: vec![],
            outputs: math::FxIndexMap::default(),
        }
    }

    /// Creates a table with the given rows and experiments, where the rows are not filled yet.
    pub fn with_rows_and_experiments<I, J>(rows: I, experiments: J) -> Self
    where
        I: IntoIterator<Item = Representative<S>>,
        J: IntoIterator<Item = Experiment<S>>,
    {
        Self {
            experiments: experiments.into_iter().collect(),
            outputs: rows.into_iter().map(|r| (r, vec![].into())).collect(),
        }
    }
}

impl<X> From<Vec<X>> for OutputRow<X> {
    fn from(value: Vec<X>) -> Self {
        Self(value)
    }
}
