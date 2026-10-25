/// Disambiguates between different acceptance types of omega automata.
pub enum OmegaAcceptanceType {
    /// Existential: some visited state has to be accepting (reachability).
    E,
    /// Universal: all visited states have to be accepting (safety).
    A,
    /// Büchi: accepting states are visited infinitely often.
    Buchi,
    /// Co-Büchi: rejecting states are visited only finitely often.
    CoBuchi,
    /// Parity: the minimal priority that is seen infinitely often has to be even.
    Parity,
    /// Rabin: there is a pair `(E, F)` such that `E` is seen finitely and `F` infinitely often.
    Rabin,
    /// Streett: for every pair `(E, F)`, if `F` is seen infinitely often, then so is `E`.
    Street,
    /// Muller: the set of colors seen infinitely often has to be one of the accepting sets.
    Muller,
}
