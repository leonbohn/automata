# automata

[![CI](https://github.com/leonbohn/automata/actions/workflows/ci.yml/badge.svg)](https://github.com/leonbohn/automata/actions/workflows/ci.yml)
![MSRV](https://img.shields.io/badge/rustc-1.88+-blue.svg)
![License](https://img.shields.io/badge/license-MIT-green.svg)

A Rust library for working with [transition systems and automata](https://en.wikipedia.org/wiki/Finite-state_machine) over finite **and** infinite words.

Build a DFA or a parity automaton in a few lines, combine automata with boolean operations, minimize them, check equivalence and inclusion, decompose them into strongly connected components, and read or write them in the [HOA](https://adl.github.io/hoaf/) format that is understood by tools like [Spot](https://spot.lre.epita.fr/).

> **Status:** `automata` is in an early (0.x) stage. The API will change between releases.

## What is in the box

- **Transition systems** with colors on states and/or edges, over simple (`char`) or propositional alphabets. Operations such as product, subset construction, quotient, restriction and recoloring are *lazy* and can be chained; collect them into a concrete transition system when needed.
- **Automata over finite words:** DFAs, Moore and Mealy machines, with boolean operations, equivalence and emptiness checks and minimization.
- **Automata over infinite words ($\omega$-automata):** deterministic Büchi, parity, Rabin and Muller automata, driven by *ultimately periodic words* `u v^ω`. Parity automata can be complemented and compared (equivalence, inclusion, witnesses).
- **Graph algorithms:** reachability, strongly connected components (Tarjan, Kosaraju), minimal representatives.
- **Congruences:** right congruences, Cayley graphs and transition profiles.
- **Interchange:** reading and writing deterministic Büchi and parity automata in the HOA format, and output in the DOT format (always available) or rendered images (opt-in features).

## Installation

`automata` is not on crates.io yet, add it as a git dependency:

```toml
[dependencies]
automata = { git = "https://github.com/leonbohn/automata" }
```

The minimum supported Rust version is **1.88**.

### Cargo features

| feature | default | description |
| ------- | ------- | ----------- |
| `hoa` | yes | reading and writing automata in the [HOA format](https://adl.github.io/hoaf/), using the [`hoars`](https://github.com/leonbohn/hoars) crate |
| `random` | no | generation of random transition systems and words |
| `render` | no | rendering automata to SVG/PNG without external tools (experimental, pulls in `resvg`, `usvg` and `layout-rs`) |
| `graphviz` | no | rendering and displaying automata with an installed [graphviz](https://graphviz.org/) `dot` executable (experimental, implies `render`) |

The textual DOT output needs no feature.

## Quick start: finite words

Automata are built with a [`Builder`](https://docs.rs/automata/latest/automata/ts/struct.Builder.html): give the colors of the states, the transitions, and turn the result into the type of automaton you want. The following DFA accepts exactly the words in which the number of `a`s is divisible by three.

```rust
use automata::ts::Builder;

let zero_mod_three = Builder::without_edge_colors()
    // the colors of the states 0, 1, 2: only state 0 is accepting
    .with_state_colors([true, false, false])
    // transitions are given as (source, symbol, target)
    .with_transitions([
        (0, 'a', 1), (0, 'b', 0),
        (1, 'a', 2), (1, 'b', 1),
        (2, 'a', 0), (2, 'b', 2),
    ])
    // the DFA has state 0 as its initial state
    .into_dfa(0);

assert!(zero_mod_three.accepts("abbabba"));
assert!(!zero_mod_three.accepts("ab"));
```

Automata can be combined with boolean operations, and compared:

```rust
use automata::ts::Builder;

fn mod_three(accepting: usize) -> automata::automaton::DFA {
    Builder::without_edge_colors()
        .with_state_colors((0..3).map(|q| q == accepting))
        .with_transitions([
            (0, 'a', 1), (0, 'b', 0),
            (1, 'a', 2), (1, 'b', 1),
            (2, 'a', 0), (2, 'b', 2),
        ])
        .into_dfa(0)
}
let zero = mod_three(0);
let one = mod_three(1);

// union, intersection and negation are computed on demand
let zero_or_one = zero.union(&one);
assert!(zero_or_one.accepts("aaa") && zero_or_one.accepts("a"));
assert!(!zero_or_one.accepts("aa"));
assert!(zero_or_one.negation().accepts("aa"));

// the two languages are disjoint and different
assert!(zero.intersection(&one).is_empty_language());
assert!(!zero.equivalent(&one));

// minimization (this DFA is already minimal)
let minimized = zero.clone().minimize();
assert!(zero.equivalent(&minimized));
```

Moore and Mealy machines can be minimized as well.

## Quick start: infinite words

Automata over infinite words read *ultimately periodic words* `u v^ω`, which consist of a finite prefix `u` (the spoke) and a finite loop `v` that is repeated forever. They are written with the `upw!` macro. A word is accepted depending on which edges are taken infinitely often. The deterministic parity automaton (DPA) below labels its edges with priorities and accepts if the smallest priority that is seen infinitely often is even.

```rust
use automata::{upw, ts::Builder};

let dpa = Builder::without_state_colors()
    // transitions are given as (source, symbol, priority, target)
    .with_transitions([
        (0, 'a', 1, 1),
        (0, 'b', 0, 0),
        (1, 'a', 1, 0),
        (1, 'b', 2, 1),
    ])
    .into_dpa(0);

// b^ω only takes the loop on state 0 with priority 0
assert!(dpa.accepts(upw!("b")));
// bb a^ω ends in a loop that sees priority 1 (and 0), the minimum is not even
assert!(!dpa.accepts(upw!("bb", "a")));

// DPAs can be complemented and compared
let complement = dpa.clone().complement();
assert!(complement.accepts(upw!("bb", "a")));
assert!(dpa.language_equivalent(&dpa.clone().complement().complement()));
assert!(!dpa.language_equivalent(&complement));

// and we can ask for a word that is accepted
let word = dpa.give_accepted_word().expect("the language is not empty");
assert!(dpa.accepts(&word));
```

Büchi, Rabin and Muller conditions are available as `DBA`, `DRA` and `DMA`; parity automata are the best supported ones.

## Transition systems and lazy operations

A DFA is a *transition system* (states connected by colored edges) together with an initial state and an acceptance condition. The transition system alone is available through the `TransitionSystem` trait, which also provides combinators that transform it **without copying**: each of them returns a new object that computes its result on demand.

```rust
use automata::{math, ts::{Builder, TransitionSystem}, representation::CollectTs};

let aut = Builder::without_edge_colors()
    .with_state_colors([true, false, true, false])
    .with_transitions([
        (0, 'a', 2), (0, 'b', 1), (0, 'c', 3),
        (1, 'a', 0), (1, 'b', 2), (1, 'c', 3),
        (2, 'a', 2), (2, 'b', 1), (2, 'c', 3),
        (3, 'a', 3), (3, 'b', 3), (3, 'c', 3),
    ])
    .into_dfa(0);

// all four states are reachable from the initial state ...
assert_eq!(
    aut.reachable_state_indices().collect::<math::Set<_>>(),
    math::Set::from_iter([0, 1, 2, 3])
);
// ... but only state 3 is reachable from state 3
assert_eq!(
    aut.reachable_state_indices_from(3).collect::<math::Set<_>>(),
    math::Set::from_iter([3])
);

// strongly connected components: {0, 1, 2} and the sink {3}
assert_eq!(aut.sccs().size(), 2);

// combinators work on references and are evaluated lazily ...
let restricted = (&aut).restrict_state_indices(|q| q < 3);
// ... until we collect the result into a concrete transition system
let collected = restricted.collect_dts();
assert_eq!(collected.size(), 3);
```

## Reading and writing HOA

With the `hoa` feature (enabled by default), deterministic Büchi and parity automata can be read from and written to the [HOA format](https://adl.github.io/hoaf/), which is understood by [Spot](https://spot.lre.epita.fr/) and many other tools. See the [`hoa` module](https://docs.rs/automata/latest/automata/hoa/index.html) for a complete example. The `oai` tool in the [frieda](https://github.com/leonbohn/frieda) repository is a small command line program built on top of it.

## DOT output and rendering

Every transition system and automaton can be turned into the [DOT](https://graphviz.org/doc/info/lang.html) format, for example to feed it into `dot -Tsvg`:

```rust
use automata::{dot::Dottable, ts::Builder};

let dfa = Builder::without_edge_colors()
    .with_state_colors([true, false])
    .with_transitions([(0, 'a', 1), (1, 'a', 0)])
    .into_dfa(0);

let dot = dfa.dot_representation();
assert!(dot.starts_with("digraph"));
assert!(dot.contains("q0 -> q1"));
```

The experimental features `render` and `graphviz` additionally render automata to images directly.

## Concepts

An **automaton** is a transition system together with an initial state and an acceptance component that decides which words are accepted.

**Alphabets.** Transition systems are generic over the alphabet. A *simple* alphabet (`CharAlphabet`) is a collection of `char`s that label both edges and transitions. A *propositional* alphabet (`PropAlphabet`) is given by atomic propositions: words consist of valuations of the propositions, and edges are labeled by boolean formulas over them (stored as BDDs). Propositional alphabets exist for the interaction with other tools through HOA; for experiments a `CharAlphabet` is simpler.

**Edges and transitions.** As in other libraries for ($\omega$-)automata, an *edge* has a source, a target, a color and a guard (an *expression* of the alphabet), while a *transition* is a concrete step on a single symbol. For simple alphabets the two coincide; for propositional alphabets an expression matches many symbols.

**Capabilities are traits.** `TransitionSystem` is the central trait. `Pointed` adds an initial state, `Deterministic` guarantees at most one transition per state and symbol, `Sproutable` and `Shrinkable` allow growing and shrinking a transition system. The default implementation behind `TS`, `DTS` and `NTS` is a linked-list based transition system.

For the theory behind all of this, see the chapters on finite automata and $\omega$-automata in the *Handbook of Automata Theory* (Pin, ed.), the open-access [thesis](https://theses.hal.science/tel-04314678v1/document) on which the design is based, or the semantics description at the bottom of the [HOA page](https://adl.github.io/hoaf/).

## Related crates

- [`hoars`](https://github.com/leonbohn/hoars): the parser for the HOA format used here.
- [`automata-learning`](https://github.com/leonbohn/automata-learning): active and passive learning algorithms for automata, built on this crate.
- [`frieda`](https://github.com/leonbohn/frieda): command line tools and experiments.

## Contributing

Contributions are welcome, please open an issue or a pull request. Before submitting, run `./scripts/check`, which executes the same checks as the CI (formatting, clippy, documentation, tests with different feature combinations). Open problems are tracked as [issues](https://github.com/leonbohn/automata/issues).

## License and acknowledgements

Licensed under the MIT license, see `LICENSE.md`. Many ideas and parts of the graph algorithms were inspired by [`petgraph`](https://github.com/petgraph/petgraph) and [`spot`](https://spot.lre.epita.fr/), thank you for your work.
