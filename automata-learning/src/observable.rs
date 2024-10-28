use automata::{
    math::Bijection,
    prelude::{Alphabet, DefaultIdType, IndexType, SimpleAlphabet, Sproutable, Symbol},
    word::FiniteWord,
    Color, RightCongruence, Void,
};

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

        let mut mr: Vec<Vec<A::Symbol>> = vec![];
        let mut symbols: Vec<A::Symbol> = self.alphabet().universe().collect();
        let mut position: DefaultIdType = 0;
        let mut access: Vec<A::Symbol> = vec![];

        while position < mr.len().try_into().unwrap() {
            'symbols: for sym in &symbols {
                access.push(*sym);

                let new_edge_color = CP::make_edge(if CP::ON_EDGES {
                    self.observe(&access)
                } else {
                    None
                });

                for target in 0..(mr.len() as DefaultIdType) {
                    if !self.separated(&access, &mr[target as usize]) {
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
                assert_eq!(new_state_id, cong.add_state(new_state_color));
                cong.add_edge((position, *sym, new_edge_color, new_state_id));
                access.pop();
            }
        }

        cong
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn observable_test() {
        assert_eq!(1, 1)
    }
}
