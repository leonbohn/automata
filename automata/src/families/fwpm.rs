use super::{Alphabet, Int, FWPM};

impl<A: Alphabet> FWPM<A, Int> {
    /// Returns a tuple containing the minimum and maximum color values that can
    /// be emitted.
    pub fn range_bounds(&self) -> impl Iterator<Item = (Int, Int)> + '_ {
        self.progress.iter().map(|(_, p)| {
            let mut cr = p.color_range();
            let Some(mut min) = cr.next() else {
                return (0, 0);
            };
            let mut max = min.clone();
            for x in p.color_range() {
                if x < min {
                    min = x.clone()
                }
                if x > max {
                    max = x.clone()
                }
            }
            (min, max)
        })
    }
    /// Gives the complexity, measured in the number of different colors that
    /// can be emitted.
    pub fn complexity(&self) -> usize {
        self.range_bounds()
            .map(|(low, high)| (high - low) as usize)
            .max()
            .unwrap_or(0)
    }
}
