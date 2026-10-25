#![allow(unused)]
use crate::alphabet::{Alphabet, CharAlphabet};
use crate::automaton::{DBA, DFA, DPA, MealyMachine, MooreMachine};
use crate::representation::IntoTs;
use crate::ts::{DefaultIdType, ForAlphabet, Shrinkable, Sproutable, StateIndex};
use crate::word::ReducedOmegaWord;
use crate::{DTS, TransitionSystem};
use crate::{Int, Void, math};
use math::sample_continuous_bernoulli;
use rand::{Rng, thread_rng};
use std::cmp::min;

/// Uses sprout-like algorithm to generate a random transition system. `symbols` determines the
/// number of distinct symbols in the [`CharAlphabet`]. `probability` determines the probability
/// of a back edge to some state being inserted. The algorithm is as follows:
/// 1. Start with a single state.
/// 2. For each symbol, go through the existing states in order and with probability `probability`
///    add a back edge that state.
/// 3. If no back edge to some state was added, we insert an edge to a new state.
/// 4. Repeat until all states and symbols have been treated.
pub fn generate_random_ts(symbols: usize, probability: f64) -> (DTS, StateIndex<DTS>) {
    let alphabet = CharAlphabet::of_size(symbols);
    let mut dts = DTS::for_alphabet(alphabet.clone());

    let mut current = dts.add_state(Void);
    let mut symbol_position = 0;
    let mut rng = thread_rng();

    'outer: loop {
        if current >= (dts.size() as DefaultIdType) {
            // we have treated all states, we can exit
            break 'outer;
        }

        if symbol_position >= symbols {
            // we have treated all symbols, go to next state
            symbol_position = 0;
            current += 1;
            continue 'outer;
        }

        let symbol = alphabet[symbol_position];
        symbol_position += 1;

        for target in 0..=current {
            let value: f64 = rng.gen_range(0.0..=1.0);
            if value < probability {
                dts.add_edge((current, symbol, target));
                continue 'outer;
            }
        }

        // no target was found so we create it
        let target = dts.add_state(Void);
        dts.add_edge((current, symbol, target));
    }

    (dts, 0)
}

/// Works as [`generate_random_ts`], but returns a [`DFA`] instead by randomly coloring the states.
pub fn generate_random_dfa(symbols: usize, probability: f64) -> DFA {
    let (ts, initial) = generate_random_ts(symbols, probability);
    ts.map_state_colors(|_| thread_rng().gen_bool(probability))
        .with_initial(initial)
        .into_dfa()
}

/// Calls [`generate_random_ts_sized`] and uses the returned transition system to build a
/// [`MealyMachine`] with colors `0..=max_color`.
pub fn generate_random_mealy(symbols: usize, max_color: usize, size: usize) -> MealyMachine {
    let (ts, initial) = generate_random_ts_sized(symbols, size);
    let mut mm = ts
        .map_edge_colors(|_| thread_rng().gen_range(0..=max_color) as Int)
        .with_initial(initial)
        .into_mealy()
        .minimize()
        .into_mealy();
    mm.trim();
    mm
}

/// Calls [`generate_random_ts_sized`] and uses the returned transition system to build a
/// [`MooreMachine`] with colors `0..=max_color`.
pub fn generate_random_moore(symbols: usize, max_color: usize, size: usize) -> MooreMachine {
    let (ts, initial) = generate_random_ts_sized(symbols, size);
    let mut mm = ts
        .map_state_colors(|_| thread_rng().gen_range(0..=max_color) as Int)
        .with_initial(initial)
        .into_moore()
        .minimize()
        .into_moore();
    mm.trim();
    mm
}

/// Generate a random deterministic transition system of size `size` by randomly drawing transitions.
/// `symbols` determines the number of distinct symbols in the [`CharAlphabet`].
/// The algorithm is as follows:
/// 1. Start with `size` states and no transitions.
/// 2. For each state, for each symbol draw a target state and add the corresponding edge
///
/// Note that depending on which state is chosen as the initial state, there may be unreachable states.
///
/// # Panics
///
/// Panics if `size` is zero or if `symbols` is 26 or more.
pub fn generate_random_ts_sized(symbols: usize, size: usize) -> (DTS, StateIndex<DTS>) {
    assert!(size > 0);
    let alphabet = CharAlphabet::of_size(symbols);
    let mut dts = DTS::for_alphabet(alphabet.clone());
    // add states
    for _ in 0..size {
        dts.add_state(Void);
    }
    // add edges
    let mut rng = thread_rng();
    for q in dts.state_indices_vec() {
        for sym in alphabet.universe() {
            let target = rng.gen_range(0..(dts.size() as DefaultIdType));
            dts.add_edge((q, sym, target));
        }
    }

    assert!(dts.contains_state_index(0));
    (dts, 0)
}

/// Works as [`generate_random_ts_sized`], but returns a [`DBA`] instead by randomly coloring the edges.
/// Removes unreachable states, that means the resulting DBA may be smaller than `size`.
/// The acceptance condition is drawn from an exponential distribution controlled by parameter `lambda`.
/// Values `lambda <= .01` approximate a uniform distribution.
pub fn generate_random_dba(symbols: usize, size: usize, lambda: f64) -> DBA {
    // draw random transition system
    let (mut dts, initial) = generate_random_ts_sized(symbols, size);
    // remove unreachable states
    dts.trim_from(initial);
    // draw acceptance condition
    dts.map_edge_colors(|_| draw_priority(2, lambda) == 0)
        .with_initial(initial)
        .into_dba()
}

/// Works as [`generate_random_ts_sized`], but returns a [`DPA`] instead by randomly
/// assigning priorities in the range `0..priorities` to each edge.
/// Removes unreachable states, that means the resulting DPA may be smaller than `size`.
/// The acceptance condition is drawn from an exponential distribution controlled by parameter `lambda`.
/// Values `lambda <= 1/20/num_prios` approximate a uniform distribution.
pub fn generate_random_dpa(symbols: usize, size: usize, num_prios: Int, lambda: f64) -> DPA {
    // draw random transition system
    let (mut dts, initial) = generate_random_ts_sized(symbols, size);
    // remove unreachable states
    dts.trim_from(initial);
    // draw acceptance condition
    dts.map_edge_colors(|_| draw_priority(num_prios, lambda))
        .with_initial(initial)
        .into_dpa()
}

/// Randomly draw a priority in range [0,num_prios) from continuous Bernoulli distribution
pub fn draw_priority(num_prios: u8, lambda: f64) -> u8 {
    let r = sample_continuous_bernoulli(lambda);
    min((r * num_prios as f64).floor() as u8, num_prios - 1)
}

/// Generate a random `String` over the universe of the `alphabet`
/// The length of the `String` is drawn uniformly from the range `min_len..=max_len`.
pub fn generate_random_word(alphabet: &CharAlphabet, min_len: usize, max_len: usize) -> String {
    let charset: Vec<char> = alphabet.universe().collect();

    let mut rng = thread_rng();
    let length = rng.gen_range(min_len..=max_len);
    let random_word: String = (0..length)
        .map(|_| {
            let idx = rng.gen_range(0..charset.len());
            charset[idx] as char
        })
        .collect();

    random_word
}

/// Generate a set of `number` random `String`s over the universe of the `alphabet`.
/// The length for each sampled word is drawn uniformly from the range `min_len..=max_len`.
pub fn generate_random_words(
    alphabet: &CharAlphabet,
    min_len: usize,
    max_len: usize,
    number: usize,
) -> math::Set<String> {
    let mut word_set = math::Set::with_capacity(number);

    while word_set.len() < number {
        let random_word = generate_random_word(alphabet, min_len, max_len);
        word_set.insert(random_word);
    }

    word_set
}

/// Generate a random `ReducedOmegaWord` over the universe of the `alphabet`.
/// The length of the spoke is drawn uniformly from the range `min_len_spoke..=max_len_spoke`.
/// The length of the cycle is drawn uniformly from the range `min_len_cycle..=max_len_cycle`.
/// Panics if the length of the cycle can be 0.
///
/// # Panics
///
/// Panics if a minimum length exceeds the corresponding maximum, or if `min_len_cycle` is zero.
pub fn generate_random_omega_word(
    alphabet: &CharAlphabet,
    min_len_spoke: usize,
    max_len_spoke: usize,
    min_len_cycle: usize,
    max_len_cycle: usize,
) -> ReducedOmegaWord<char> {
    assert!(min_len_spoke <= max_len_spoke);
    assert!(min_len_cycle <= max_len_cycle);
    assert!(min_len_cycle > 0);

    let spoke = generate_random_word(alphabet, min_len_spoke, max_len_spoke);
    let cycle = generate_random_word(alphabet, min_len_cycle, max_len_cycle);

    upw!(spoke, cycle)
}

/// Generate a set of `number` random `ReducedOmegaWord`s over the universe of the `alphabet`.
/// The length for each spoke is drawn uniformly from the range `min_len_spoke..=max_len_spoke`.
/// The length for each cycle is drawn uniformly from the range `min_len_cycle..=max_len_cycle`.
/// Panics if the length of the cycle can be 0.
pub fn generate_random_omega_words(
    alphabet: &CharAlphabet,
    min_len_spoke: usize,
    max_len_spoke: usize,
    min_len_cycle: usize,
    max_len_cycle: usize,
    number: usize,
) -> math::Set<ReducedOmegaWord<char>> {
    let mut word_set = math::Set::with_capacity(number);

    while word_set.len() < number {
        let random_word = generate_random_omega_word(
            alphabet,
            min_len_spoke,
            max_len_spoke,
            min_len_cycle,
            max_len_cycle,
        );
        word_set.insert(random_word);
    }

    word_set
}

#[cfg(test)]
mod tests {
    use super::{
        generate_random_dba, generate_random_dpa, generate_random_omega_words,
        generate_random_ts_sized, generate_random_words,
    };
    use crate::{TransitionSystem, random::CharAlphabet};

    #[test]
    fn random_ts_sized() {
        let (dts, _initial) = generate_random_ts_sized(2, 4);
        assert_eq!(dts.size(), 4);
    }

    #[test]
    fn random_dba_sized() {
        let dba = generate_random_dba(2, 10, 0.99);
        assert!(dba.size() <= 10);
    }

    #[test]
    fn random_dpa_sized() {
        let dpa = generate_random_dpa(2, 10, 3, 0.5);
        assert!(dpa.size() <= 10);
    }

    #[test]
    fn random_words() {
        let alphabet = CharAlphabet::of_size(2);
        let word_set = generate_random_words(&alphabet, 1, 10, 20);
        let omega_word_set = generate_random_omega_words(&alphabet, 0, 5, 1, 5, 20);

        assert_eq!(word_set.len(), 20);
        assert_eq!(omega_word_set.len(), 20);
    }
}
