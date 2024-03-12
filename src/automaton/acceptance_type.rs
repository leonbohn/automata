/// Disambiguates between different acceptance types of omega automata.
#[allow(missing_docs)]
pub enum OmegaAcceptanceType {
    E,
    A,
    Buchi,
    CoBuchi,
    Parity,
    Rabin,
    Street,
    Muller,
}
