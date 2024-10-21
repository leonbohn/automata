use automata::{
    math::Bijection,
    prelude::{Alphabet, DefaultIdType, IndexType, SimpleAlphabet, Symbol},
    word::FiniteWord,
    Color, RightCongruence, Void,
};

pub trait ColorPosition {
    const ON_EDGES: bool;
    type Edge<C: Color>: Color;
    type State<C: Color>: Color;
    fn make_edge<C: Color>(c: Option<C>) -> Self::Edge<C>;
    fn make_state<C: Color>(c: Option<C>) -> Self::State<C>;
}
pub struct StateColored;
pub struct EdgeColored;
impl ColorPosition for EdgeColored {
    const ON_EDGES: bool = true;
    type Edge<C> = C;
    type State<C> = Void;

    fn make_edge<C: Color>(c: Option<C>) -> Self::Edge<C> {
        c.unwrap()
    }

    fn make_state<C: Color>(c: Option<C>) -> Self::State<C> {
        Void
    }
}
impl ColorPosition for StateColored {
    const ON_EDGES: bool = false;
    type Edge<C> = Void;
    type State<C> = C;

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
    fn color(&self, x: impl FiniteWord<Symbol = A::Symbol>) -> Self::C;

    fn right_congruence(self) -> RightCongruence<A, CP::State<Self::C>, CP::Edge<Self::C>> {
        let mut cong = RightCongruence::new(self.alphabet().clone());
        let mut mr = vec![];
        let mut symbols = self.alphabet().universe().collect();
        let mut positio: DefaultIdType = 0;

        while position < mr.len() {
            'symbols: for sym in &symbols {
                access.push(*sym);
                for target in 0..mr.len() {
                    if !self.separated(&access, &mr[target]) {
                        let edge_color = if CP::ON_EDGES {
                            Some(self.color(&access))
                        } else {
                            None
                        };
                        cong.add_edge((position, target, CP::make_edge(edge_color), 0));
                        access.pop();
                        continue 'symbols;
                    }
                }
                let q = self.observe(&access);

                if let Some(id) = access.iter().position(|a| a == &q) {
                    let edge_color = if CP::ON_EDGES {
                        Some(self.color(&access))
                    } else {
                        None
                    };
                    cong.add_edge((
                        position,
                        *sym,
                        CP::make_edge(edge_color),
                        id as DefaultIdType,
                    ));
                } else {
                    let id = access.len();
                    mr.push(id);
                    access.push(q);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn observable_test() {
        assert_eq!(1, 1)
    }
}
