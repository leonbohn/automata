use crate::prelude::Symbol;

pub struct KleeneStar<S> {
    symbols: Vec<S>,
    current: Vec<usize>,
}

impl<S: Symbol> Iterator for KleeneStar<S> {
    type Item = Vec<S>;
    fn next(&mut self) -> Option<Self::Item> {
        let out = self.current.iter().map(|i| self.symbols[*i]).collect();

        let mut carry = true;
        let mut i = self.current.len();
        while carry && i > 0 {
            i -= 1;
            self.current[i] += 1;
            if self.current[i] >= self.symbols.len() {
                self.current[i] = 0;
                carry = true;
            } else {
                carry = false;
            }
        }

        if carry {
            self.current = std::iter::repeat(0).take(self.current.len() + 1).collect();
        }

        Some(out)
    }
}

impl<S> KleeneStar<S> {
    pub fn new(symbols: Vec<S>) -> Self {
        Self {
            symbols,
            current: vec![],
        }
    }
    pub fn non_empty(symbols: Vec<S>) -> Self {
        assert!(!symbols.is_empty(), "need at least one symbol");
        Self {
            symbols,
            current: vec![0],
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::kleene::KleeneStar;

    #[test]
    fn kleene_star() {
        assert_eq!(
            KleeneStar::new(vec!['a', 'b'])
                .take_while(|e| e.len() <= 2)
                .collect::<Vec<_>>(),
            vec![
                vec![],
                vec!['a'],
                vec!['b'],
                vec!['a', 'a'],
                vec!['a', 'b'],
                vec!['b', 'a'],
                vec!['b', 'b']
            ]
        );
    }
}
