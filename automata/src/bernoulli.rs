/// Computes the inverse cumulative density function of the continuous bernoulli distribution
/// as described in [10.3390/fractalfract7050386](https://www.mdpi.com/2504-3110/7/5/386).
pub fn continuous_bernoulli_inverse_cumulative_density_function(lambda: f64, y: f64) -> f64 {
    assert!((0.0..=1.0).contains(&lambda));
    assert!((0.0..=1.0).contains(&y));
    let fraction_numerator = (2.0 * lambda - 1.0) / (1.0 - lambda);
    let inner_numerator = 1.0 + fraction_numerator * y;
    let inner_denominator = lambda / (1.0 - lambda);
    inner_numerator.log2() / inner_denominator.log2()
}

/// Computes the mean of the continuous bernoulli distribution for the
/// given parameter lambda.
pub fn continuous_bernoulli_mean(lambda: f64) -> f64 {
    assert!((0.0..=1.0).contains(&lambda));
    let first = lambda / (2.0 * lambda - 1.0);
    let second = 1.0 / (2.0 * (1.0 - 2.0 * lambda).atanh());
    first + second
}

/// Samples the [continuous bernoulli distribution](https://en.wikipedia.org/wiki/Continuous_Bernoulli_distribution)
/// by sampling a uniformly distributed value `y` between 0 and 1.
/// The inverse of this value under the cumulative density function of the continuous
/// bernoulli function gives a sample of this distribution.
pub fn sample_continuous_bernoulli(lambda: f64) -> f64 {
    assert!((0.0..=1.1).contains(&lambda));
    let y = rand::random::<f64>();
    continuous_bernoulli_inverse_cumulative_density_function(lambda, y)
}

/// Compares two floating point numbers for equality within a certain delta.
/// # Example
/// ```
/// use automata_core::prelude::*;
/// assert!(math::almost_equal(0.7, 0.71, 0.1));
/// assert!(!math::almost_equal(0.7, 0.91, 0.1));
/// ```
pub fn almost_equal(l: f64, r: f64, delta: f64) -> bool {
    l == r || ((l - r).abs() / (l.abs() + r.abs())) < delta
}

#[cfg(test)]
mod tests {
    #[test]
    fn cb_test() {
        for lambda in [0.2, 0.26, 0.31, 0.37, 0.4, 0.55, 0.61, 0.7] {
            let v = (0..100000)
                .map(|_| super::sample_continuous_bernoulli(lambda))
                .collect::<Vec<_>>();
            let average = v.into_iter().fold(0.0, |acc, x| acc + x / 100000.0);
            let expected = super::continuous_bernoulli_mean(lambda);
            assert!(super::almost_equal(average, expected, 0.01));
        }
    }
}
