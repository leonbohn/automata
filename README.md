# automata

[![CI](https://github.com/leonbohn/automata/actions/workflows/ci.yml/badge.svg)](https://github.com/leonbohn/automata/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/automata.svg)](https://crates.io/crates/automata)
[![docs.rs](https://img.shields.io/docsrs/automata)](https://docs.rs/automata)
![MSRV](https://img.shields.io/badge/rustc-1.88+-blue.svg)
![License](https://img.shields.io/badge/license-MIT-green.svg)

A Rust crate for topics from [automata theory](https://en.wikipedia.org/wiki/Automata_theory), in particular it provides tools to work with [transition systems](https://en.wikipedia.org/wiki/Transition_system) and [finite state machines](https://en.wikipedia.org/wiki/Finite-state_machine).
It aims to cover both [finite word automata](https://en.wikipedia.org/wiki/Deterministic_finite_automaton) and [$\omega$-automata](https://en.wikipedia.org/wiki/%CE%A9-automaton) working on infinite words.
On top of primitives and algorithms for their manipulation, the crate also provides some methods for input and output of $\omega$-automata in the [HOA](https://adl.github.io/hoaf/) format.
It can also produce a [graphviz](https://graphviz.org/) representation and turn that into graphics.

The aim is to have good ergonomics while also being conscious of performance, which is [actively measured](https://bench.lnbhn.xyz/).
To achieve this, the crate follows the style of the standard library, providing lazy adaptors for transition systems, which can be collected into an actual manifestation to avoid the overhead of the indirections this introduces.

> As the version number indicates, this crate is in a very early stage and will might see some drastic breaking changes in the future.

# Summary of what `automata` contains

- A model of **Transition systems** with coloured states and/or edges
, over both simple char-based and over propositional alphabets.
- Operations on transition systems such as products, quotiens, restrictions, or mappings of edges. Each operation is *lazy* and produces a view of the result of the modification, but it can be collected into a manifiestation when needed.
- **Automata over finite words:** automata with outputs on the state-level ([Moore machines](https://en.wikipedia.org/wiki/Moore_machine)) and ones which produce output at edges ([Mealy machines](https://en.wikipedia.org/wiki/Mealy_machine)). For [DFAs](https://en.wikipedia.org/wiki/Deterministic_finite_automaton), which are a special case of the former, boolean operations are available, as well as equivalence and emptiness checks. Moreover, refinement-based algorithms for the minimization of finite-word automata are available.
- **Automata over infinite words:** deterministic Büchi, parity, Rabin, Streett and Muller automata are available. The crate mainly focuses on deterministic parity automata with edge-based acceptance. But an aim for the future would be to be comprehensive and support all kinds of $\omega$-automata. Right now, only parity automata can be complemented and compared (equivalence, inclusion, witnesses).
- **Graph algorithms:** reachability, strongly connected components (Tarjan, Kosaraju), minimal representatives reaching the reachable states of a transition system from a given state.
- **Congruences:** right congruences, Cayley graphs and transition profiles.
- **Input and Output:** reading and writing deterministic Büchi and parity automata in the HOA format, and output in the DOT format (always available) or rendered images (opt-in features).

## Getting Started

Since `automata` has been published on crates.io, it is as easy as using Rust version *1.88* or newer, and adding the following to the manifest:
```toml
[dependencies]
automata = { version = "0.2" }
```

It makes sense to import the full prelude, which brings most commonly used traits and types into scope.
We can then use the [`Builder`](https://docs.rs/automata/latest/automata/ts/struct.Builder.html) to construct a transition system or automaton.
For example the following code could be used to construct a DFA over the alphabet {`a`,`b`} which recognises precisely those words in which the number of `a` is divisible by three.

### Cargo features

| feature | default | description |
| ------- | ------- | ----------- |
| `hoa` | yes | reading and writing automata in the [HOA format](https://adl.github.io/hoaf/), using the [`hoars`](https://github.com/leonbohn/hoars) crate |
| `families` | no | families of DFAs and of weak priority mappings (FDFA, FWPM) indexed by a right congruence, and the conversions between them |
| `learning` | no | experimental: passive (sprout, DPAInf) and active (L\*) learning of automata, see `automata::learning` (implies `families`) |
| `random` | no | generation of random transition systems and words |
| `render` | no | rendering automata to SVG/PNG and `data:` URLs without external tools, and displaying them in the viewer of the system (experimental, pulls in `resvg`, `usvg` and `layout-rs`) |
| `graphviz` | no | the same with an installed [graphviz](https://graphviz.org/) `dot` executable (experimental, independent of `render`, recommended, nicer layouts) |

The textual DOT output needs no feature.

## Using the crate

```rust
use automata::prelude::*;

// create a builder for automaton without edge labels
let zero_mod_three = Builder::without_edge_colors()
    // give colours of states, only state 0 is accepting
    .with_state_colors([true, false, false])
    // list out transitions, no edge colour required
    .with_transitions([
        (0, 'a', 1), (0, 'b', 0),
        (1, 'a', 2), (1, 'b', 1),
        (2, 'a', 0), (2, 'b', 2),
    ])
    // construct a dfa with the given initial state
    .into_dfa(0);

// test out its behaviour
assert!(zero_mod_three.accepts("abbabba"));
assert!(!zero_mod_three.accepts("ab"));
```

Combining automata with boolean operations or comparing them is easy:

```rust
use automata::prelude::*;

// gives DFA for words where number of `a` has remainder `rem` on division by 3
// but it duplicates each state, cycling between the copies
fn mod_three(rem: usize) -> automata::automaton::DFA {
    Builder::without_edge_colors()
        .with_state_colors((0..3).map(|q| q == rem))
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
assert!(Emptiness::of(&zero.intersection(&one)).holds());
assert!(!Equivalence::of(&zero).and(&one).holds());

// the dfa is already minimized though...
let minimized = zero.clone().minimize();
assert_eq!(minimized.state_count(), 3);
assert!(Equivalence::of(&zero).and(&minimized).holds());
```

### Infinite Words

Automata over infinite words read *ultimately periodic words* $ux^\omega$ consisting of a finite prefix $u$ called spoke, and a repeating periodic suffix $v$ called teh loop.
We write them with the `upw!` macro, and acceptance of such a word is determined by considering the set of edges that it takes infinitely often.
While an equivalent formalism can be obtained by considering the set of states visited infinitely often, we opt for the more sensible option of edge-based acceptance here.
Deterministic parity automata (DPAs) have integers as edge labels and accept if the least priority seen infinitely often is even.
The DPA we construct below accepts all words which contain `a` infinitely often or `b` finitely often.

```rust
use automata::prelude::*;

// we do not need state colours because edge-based acceptance
let inf_a_or_fin_b = Builder::without_state_colors()
    // list out transitions as (source, symbol, priority, target)
    .with_transitions([
        (0, 'a', 0, 0),
        (0, 'b', 1, 0),
        (0, 'c', 2, 0),
    ])
    // and construct a DPA with initial state 0
    .into_dpa(0);

// upw!(x) creates the ultimately periodic word xxxxxx...
assert!(inf_a_or_fin_b.accepts(upw!("a")));
// upw!(u, x) creates uxxxxxxx...
assert!(!inf_a_or_fin_b.accepts(upw!("cab", "cb")));
assert!(inf_a_or_fin_b.accepts(upw!("abba", "c")));

// we can also complement and compare DPAs
let complement = inf_a_or_fin_b.clone().complement();
assert!(!complement.accepts(upw!("bb", "a")));
assert!(Equivalence::of(&inf_a_or_fin_b).and(&inf_a_or_fin_b.clone().complement().complement()).holds());
assert!(!Equivalence::of(&inf_a_or_fin_b).and(&complement).holds());

// or ask for a word witnessing non-emptiness of the accepted language
let word = Emptiness::of(&inf_a_or_fin_b).witness().expect("the language is not empty");
assert!(inf_a_or_fin_b.accepts(&word));
```
Automata using other acceptance conditions are also available through commonly used acronyms.
However DPAs are the best supported and most used ones.

More runnable programs are in the [`examples/`](https://github.com/leonbohn/automata/tree/main/examples) directory, for example `cargo run --example dfa` or `cargo run --example parity`.
Similarly, one can have a look at the [`benches/`](https://github.com/leonbohn/automata/tree/main/benches) directory or at the tests.

### Transition systems and lazy operations

A DFA is a *transition system* (states connected by colored edges) together with an initial state and an acceptance condition. The transition system alone is available through the `TransitionSystem` trait, which also provides combinators that transform it **without copying**: each of them returns a new object that computes its result on demand.

```rust
use automata::ts::q;
use automata::{DTS, math, ts::{Builder, Sccs, States, TransitionSystem}, representation::IntoTransitions};

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
    aut.reachable_state_indices().collect::<math::FxIndexSet<_>>(),
    math::FxIndexSet::from_iter([q(0), q(1), q(2), q(3)])
);
// ... but only state 3 is reachable from state 3
assert_eq!(
    aut.reachable_state_indices_from(q(3)).collect::<math::FxIndexSet<_>>(),
    math::FxIndexSet::from_iter([q(3)])
);

// strongly connected components: {0, 1, 2} and the sink {3}
assert_eq!(Sccs::on(&aut).compute().size(), 2);

// combinators work on references and are evaluated lazily ...
let restricted = (&aut).restrict_state_indices(|s| s < q(3));
// ... until we collect the result into a concrete transition system
let collected: DTS<_, _, _> = restricted.collect();
assert_eq!(collected.state_count(), 3);
```

### Reading and writing HOA

With the `hoa` feature (enabled by default), deterministic Büchi and parity automata can be read from and written to the [HOA format](https://adl.github.io/hoaf/), which is understood by [Spot](https://spot.lre.epita.fr/) and many other tools. See the [`hoa` module](https://docs.rs/automata/latest/automata/hoa/index.html) for a complete example. The `oai` tool in the [frieda](https://github.com/leonbohn/frieda) repository is a small command line program built on top of it.

### DOT output and rendering

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
Of those two, we would strongly advise to use `graphviz` since it produces better layouts and is the de-facto standard.
It does, however, require you to have [graphviz](https://graphviz.org/) installed and available in the `PATH`.
In contrast, `render` needs no external tools, but its layouts are simpler and it is less tested.
Both have only really been tried on Linux and the CI only checks that `render` and `graphviz` build and pass their tests on Linux, not on macOS or Windows. Opening an image in a viewer needs a desktop environment with a default program for SVG files.
Both offer the same operations, the `graphviz` variants carry the suffix `_graphviz`:

| | `render` (pure Rust, `layout-rs`) | `graphviz` (needs `dot` in the `PATH`) |
| --- | --- | --- |
| SVG document | `try_svg()` | `try_svg_graphviz()` |
| `data:` URL | `try_data_url()` | `try_data_url_graphviz()` |
| PNG bytes | `render()` | `render_graphviz()` |
| open in a viewer | `display_rendered()` | `display_rendered_graphviz()` |

`render_to_file_name` (`graphviz`) writes the result of `dot` to a file, the format is taken from the extension.
Displaying writes an SVG to a temporary file and opens it with the default program of your system (`xdg-open`, `open` or `start`).
Set the environment variable `IMAGE_VIEWER` to use a different program, it is called with the path of the file.

## Concepts

An **automaton** is a transition system together with an initial state and an acceptance component that decides which words are accepted.

**Alphabets.** Transition systems are generic over the alphabet. A *simple* alphabet (`CharAlphabet`) is a collection of `char`s that label both edges and transitions. A *propositional* alphabet (`PropAlphabet`) is given by atomic propositions: words consist of valuations of the propositions, and edges are labeled by boolean formulas over them (stored as BDDs). Propositional alphabets exist for the interaction with other tools through HOA; for experiments a `CharAlphabet` is simpler.

**Edges and transitions.** Each *edge* has a source, a target, a color and a guard (an *expression* of the alphabet), while a *transition* is a concrete step on a single symbol. For simple alphabets the two coincide; for propositional alphabets an expression matches many symbols. Every storage and every adapter hands its edges out as the same `ts::EdgeRef` (`source`, `target`, `expression`, `color`), so generic code does not multiply over edge types.

**Recoloring.** `map_state_colors`, `map_edge_colors`, `map_edge_colors_full`, `with_state_color` and the `erase_*` methods all return the same adapter, which computes the new colors on access and caches nothing, just like `Iterator::map`.

**Capabilities are traits.** `TransitionSystem` is the central trait. `Pointed` adds an initial state, `Deterministic` guarantees at most one transition per state and symbol, `Sproutable` and `Shrinkable` allow growing and shrinking a transition system. The default implementation is `LinkedTs`, a linked-list based transition system with stable edge ids; `NTS` is `LinkedTs` and `DTS` is `Det<LinkedTs>`, where `Det` makes determinism part of the type.

For the theory behind all of this, see the chapters on finite automata and $\omega$-automata in the *Handbook of Automata Theory* (Pin, ed.), the open-access [thesis](https://theses.hal.science/tel-04314678v1/document) on which the design is based, or the semantics description at the bottom of the [HOA page](https://adl.github.io/hoaf/).

## Benchmarks

The code is actively benchmarked, see code under [`benches/`](https://github.com/leonbohn/automata/tree/main/benches).
This is run on a VPS and a dashboard with graphs can be viewed [here](https://bench.lnbhn.xyz/).

## Contributing

Of course we welcome any and all contributions.
Be it just fixing a typo, reporting an issue, or contributing some code.
But we want to ensure code quality, and thus require you to submit a pull request.
Before submitting, you should run `./scripts/check` which executes clippy, builds, checks for formatting or documentation issues, and runs tests in various feature combinations.
This test is run whenever a PR is opened, but you can save some time by doing it locally yourself.

## License and acknowledgements

An AI has been used in the development of this crate.
Mainly in the process of consolidating previous efforts into a coherent library, as well as in the identification of optimizations.
However the code itself has been reviewed, we do not simply copy and paste.
This is not supposed to be slop, instead we want to make best use of the available tools.

Licensed under the MIT license, see `LICENSE.md`. Many ideas and parts of the graph algorithms were inspired by [`petgraph`](https://github.com/petgraph/petgraph) and [`spot`](https://spot.lre.epita.fr/), thank you for your work.

