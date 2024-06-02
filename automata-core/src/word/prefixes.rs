use crate::prelude::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Subwords<'a, S: Symbol = char> {
    buf: &'a [S],
    bounds: [Id; 2],
    op: [Id; 2],
}

impl<'a, S: Symbol> Iterator for Subwords<'a, S> {
    type Item = &'a [S];

    fn next(&mut self) -> Option<Self::Item> {
        if self.bounds[0] < self.bounds[1] {
            let out = &self.buf[(self.bounds[0] as usize)..(self.bounds[1] as usize)];
            self.bounds[0] += self.op[0];
            self.bounds[1] -= self.op[1];
            Some(out)
        } else {
            None
        }
    }
}

impl<'a, S: Symbol> Subwords<'a, S> {
    pub fn new(
        buf: &'a [S],
        left_start: Id,
        right_start: Id,
        left_increment: Id,
        right_decrement: Id,
    ) -> Self {
        debug_assert!(std::mem::size_of::<Id>() <= std::mem::size_of::<usize>());

        assert!(left_start as usize <= buf.len());
        assert!(right_start as usize <= buf.len());
        Self {
            bounds: [left_start, right_start],
            buf,
            op: [left_increment, right_decrement],
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn prefixes_test() {
        let word = "abbccb";
    }
}
