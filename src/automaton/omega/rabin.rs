use std::collections::BTreeSet;

use crate::math::Set;
use crate::prelude::*;

pub type DRA<A = CharAlphabet, C = usize> = Automaton<DTS<A, Void, C>, RabinSemantics<C>, true>;
pub type IntoDRA<T> = Automaton<T, RabinSemantics<EdgeColor<T>>, true>;

#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct RabinSemantics<C: Color>(Set<RabinPair<C>>);

impl<C, I> From<I> for RabinSemantics<C>
where
    C: Color,
    I: IntoIterator<Item = RabinPair<C>>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

#[derive(Debug, Default, Clone, Eq, PartialEq, Hash)]
pub struct RabinPair<C> {
    pub(crate) fin: BTreeSet<C>,
    pub(crate) inf: BTreeSet<C>,
}

impl<C: Color> RabinPair<C> {
    pub fn new(fin: BTreeSet<C>, inf: BTreeSet<C>) -> Self {
        Self { fin, inf }
    }

    pub fn from_iters<I, J>(fin: I, inf: J) -> Self
    where
        I: IntoIterator<Item = C>,
        J: IntoIterator<Item = C>,
    {
        Self {
            fin: fin.into_iter().collect(),
            inf: inf.into_iter().collect(),
        }
    }

    pub fn satisfied_by(&self, colors: &BTreeSet<C>) -> bool {
        self.fin.intersection(colors).next().is_none()
            && self.inf.intersection(colors).next().is_some()
    }
}

impl<Q, C: Color> Semantics<Q, C> for RabinSemantics<C> {
    type Output = bool;
}

impl<Q, C: Color> OmegaSemantics<Q, C> for RabinSemantics<C> {
    fn evaluate<R>(&self, run: R) -> Self::Output
    where
        R: OmegaRun<StateColor = Q, EdgeColor = C>,
    {
        let Some(colors) = run.recurring_edge_colors_iter() else {
            return false;
        };
        let colorset = colors.collect();

        self.0.iter().any(|pair| pair.satisfied_by(&colorset))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rabin_pairs() {
        let pair = RabinPair::from_iters([1], [2]);
        let mut colors = vec![1, 2].into_iter().collect();
        assert!(!pair.satisfied_by(&colors));
        colors.remove(&1);
        assert!(pair.satisfied_by(&colors));
        colors.remove(&2);
        assert!(!pair.satisfied_by(&colors));
        colors.insert(1);
        assert!(!pair.satisfied_by(&colors));
    }

    #[test]
    fn rabin_automaton() {
        let ts = TSBuilder::without_state_colors()
            .with_transitions([
                (0, 'a', 0, 0),
                (0, 'b', 1, 1),
                (1, 'a', 0, 0),
                (1, 'b', 1, 1),
            ])
            .into_dts();
        let dra = DRA::from_parts_with_acceptance(ts, 0, [RabinPair::from_iters([], [1])].into());
        assert!(dra.accepts(upw!("ba")));
        assert!(!dra.accepts(upw!("a")));
        assert!(dra.accepts(upw!("ab")));
    }
}
