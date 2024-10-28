use std::marker::PhantomData;

use automata::{
    math::Bijection,
    prelude::{Alphabet, DefaultIdType, IndexType, SimpleAlphabet, Sproutable, Symbol},
    word::FiniteWord,
    Color, RightCongruence, Void,
};
use tracing::trace;

pub trait ColorPosition {
    const ON_EDGES: bool;
    type Edge<C: Color>: std::hash::Hash + Eq + Clone + std::fmt::Debug;
    type State<C: Color>: std::hash::Hash + Eq + Clone + std::fmt::Debug;
    fn make_edge<C: Color>(c: Option<C>) -> Self::Edge<C>;
    fn make_state<C: Color>(c: Option<C>) -> Self::State<C>;
}
pub struct StateColored;
pub struct EdgeColored;
impl ColorPosition for EdgeColored {
    const ON_EDGES: bool = true;
    type Edge<C: Color> = C;
    type State<C: Color> = Void;

    fn make_edge<C: Color>(c: Option<C>) -> Self::Edge<C> {
        c.unwrap()
    }

    fn make_state<C: Color>(c: Option<C>) -> Self::State<C> {
        Void
    }
}
impl ColorPosition for StateColored {
    const ON_EDGES: bool = false;
    type Edge<C: Color> = Void;
    type State<C: Color> = C;

    fn make_edge<C: Color>(c: Option<C>) -> Self::Edge<C> {
        Void
    }

    fn make_state<C: Color>(c: Option<C>) -> Self::State<C> {
        c.unwrap()
    }
}

pub trait Observable<A: SimpleAlphabet, CP: ColorPosition> {
    type C: Color;
    fn alphabet(&self) -> &A;

    fn separated(&self, x: &[A::Symbol], y: &[A::Symbol]) -> bool;
    fn observe(&self, x: &[A::Symbol]) -> Option<Self::C>;

    fn right_congruence(&self) -> RightCongruence<A, CP::State<Self::C>, CP::Edge<Self::C>> {
        let initial_color = if CP::ON_EDGES {
            CP::make_state(None)
        } else {
            CP::make_state(self.observe(&[]))
        };
        let mut cong: RightCongruence<A, CP::State<Self::C>, CP::Edge<Self::C>> =
            RightCongruence::new_with_initial_color(self.alphabet().clone(), initial_color);

        let mut mr: Vec<Vec<A::Symbol>> = vec![vec![]];
        let mut symbols: Vec<A::Symbol> = self.alphabet().universe().collect();
        let mut i = 0;

        while i < mr.len() {
            let mut access = mr[i].clone();
            i += 1;
            let position = (i - 1) as DefaultIdType;
            'symbols: for sym in &symbols {
                access.push(*sym);

                let new_edge_color = CP::make_edge(if CP::ON_EDGES {
                    self.observe(&access)
                } else {
                    None
                });

                for target in 0..(mr.len() as DefaultIdType) {
                    if !self.separated(&access, &mr[target as usize]) {
                        trace!("adding edge {position} --{sym:?}|{new_edge_color:?}--> {target}",);
                        cong.add_edge((position, *sym, new_edge_color, target));
                        access.pop();
                        continue 'symbols;
                    }
                }

                let new_state_color = CP::make_state(if CP::ON_EDGES {
                    None
                } else {
                    self.observe(&access)
                });
                let new_state_id = access.len() as DefaultIdType;
                mr.push(access.clone());
                trace!("adding new state {new_state_id}/{access:?}/{new_state_color:?} reached on {sym:?} from {position}");
                assert_eq!(new_state_id, cong.add_state(new_state_color));
                cong.add_edge((position, *sym, new_edge_color, new_state_id));
                access.pop();
            }
        }

        cong
    }
}

struct LengthModulusEqual<A: SimpleAlphabet, CP: ColorPosition> {
    alphabet: A,
    modulus: usize,
    remainder: usize,
    _pd: PhantomData<CP>,
}

impl<A: SimpleAlphabet, CP: ColorPosition> LengthModulusEqual<A, CP> {
    fn new(alphabet: A, modulus: usize, remainder: usize) -> Self {
        assert!(modulus > 0);
        Self {
            alphabet,
            modulus,
            remainder,
            _pd: PhantomData,
        }
    }
}

impl<A: SimpleAlphabet, CP: ColorPosition> Observable<A, CP> for LengthModulusEqual<A, CP> {
    type C = bool;

    fn alphabet(&self) -> &A {
        &self.alphabet
    }

    fn separated(&self, x: &[<A>::Symbol], y: &[<A>::Symbol]) -> bool {
        (x.len() % self.modulus) != (y.len() % self.modulus)
    }

    fn observe(&self, x: &[<A>::Symbol]) -> Option<Self::C> {
        Some((x.len() % self.modulus) == self.remainder)
    }
}

#[cfg(test)]
mod tests {
    use automata::{prelude::CharAlphabet, Dottable};
    use tracing::info;

    use crate::observable::{LengthModulusEqual, Observable, StateColored};

    #[test_log::test]
    pub fn observe_mod_eq_k() {
        let alphabet = CharAlphabet::of_size(3);
        let modulus = 120;
        let remainder = 5;

        let start = std::time::Instant::now();
        let edge_colored =
            LengthModulusEqual::<_, StateColored>::new(alphabet.clone(), modulus, remainder);
        let cong_b = edge_colored.right_congruence();
        let second = start.elapsed().as_micros();

        let start = std::time::Instant::now();
        let state_colored =
            LengthModulusEqual::<_, StateColored>::new(alphabet.clone(), modulus, remainder);
        let cong_a = state_colored.right_congruence();
        let first = start.elapsed().as_micros();

        info!("took {first}µs for Moore and {second}µs for Mealy length mod {modulus} equals {remainder}");
        // cong_a.display_rendered();
        // cong_b.display_rendered();
    }
}
