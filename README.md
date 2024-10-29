# automata

This is a library concerned with [transition systems and automata](https://en.wikipedia.org/wiki/Finite-state_machine) for both finite and infinite words.
Provides datastructures, operations (think product, subset, mapping of edge/state colors, restriction, ...) for transition systems, acceptance conditions, congruence relations as well as some reachability theoretic operations on transition systems in general.

Guaranteed to be incomplete and very much work in progress (for more than a year yay).

## Some examples
are the best way of getting a feel for working with a library which has been set up as is outlined below. Then we create for example a [DFA](https://en.wikipedia.org/wiki/Deterministic_finite_automaton) as follows.
```rust
use automata::ts::TSBuilder;

// we use a builder for creating a transition system, the edges are not colored
let zero_mod_three_times_a = TSBuilder::without_edge_colors()
    // we give the colors of our three states (position in the given collection determins state id)
    //         State:    0      1      2
    .with_state_colors([true, false, false])
    // a collection of transitions of the form (source, symbol, target) is added
    .with_transitions([(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 1), (2, 'a', 0), (2, 'b', 2)])
    // we execute the building to get a DFA with initial state 0
    .into_dfa(0);
```

Each state in a transition system has an index, which defaults to `usize` but may be more complex.
The code gives us a DFA
- with an initial state $0$
- the only accepting state is state $0$ (as it is the only one colored `true`) 
- state $0$ lies on an $a$-cycle of length $3$ and each state along this cycle has a self-loop on $b$.

We can now perform operations, for example we can test whether a word is accepted by calling the `accepts` method:
```rust ignore
assert!(zero_mod_three_times_a.accepts("abbabbababbbbabbbababbababbabbbbabbbbabbabbbbabbab")); // made you count
```
Or if we had a second DFA, `one_mod_three_times_a`, which is entirely the same, apart from swapping the colors for state $0$ and state $1$, then we could combine the two and perform operations on the result:
```rust ignore
let what_is_still_missing = zero_mod_three_times_a.union(one_mod_three_times_a.negation());
assert!(what_is_still_missing.accepts(""));
assert!(!what_is_still_missing.accepts("a"));
assert!(what_is_still_missing.accepts("aa"));
```

### Determinism, initial states and congruence relations

Most of the times, when we work with automata, we have a transition system and a dedicated initial state, meaning they implement `TransitionSystem` and `Pointed`.
While the library defines types for dealing with nondeterministic transition systems, a lot of code is focused on ts that are *deterministic*, meaning for each state and symbol, there is at most one possible edge.

This is indicated by a type if it implements the `Deterministic` trait and sice we are often interested in objects with these properties, all three traits are summarized in the `Congruence` trait.
This allows us to perform additional operations

```rust
use automata::{core::math, ts::{TSBuilder, TransitionSystem}};

let aut = TSBuilder::without_edge_colors()
    .with_state_colors([true, false, true, false])
    .with_transitions([(0, 'a', 2), (0, 'b', 1), (0, 'c', 3),
                       (1, 'a', 0), (1, 'b', 2), (1, 'c', 3),
                       (2, 'a', 2), (2, 'b', 1), (2, 'c', 3),
                       (3, 'a', 3), (3, 'b', 3), (3, 'c', 3) ])
    .into_dfa(0);

// reachable states in lenght-lexicographic order
assert_eq!(aut.reachable_state_indices().collect::<math::Set<_>>(), math::Set::from_iter([0, 1, 2, 3]));
// but we can also just pick a different starting state
assert_eq!(aut.reachable_state_indices_from(3).collect::<math::Set<_>>(), math::Set::from_iter([3]));
```

Operations can be chained together efficiently and are evaluated as needed.
They are lazily evaluated and computations only happen if the result is actually needed.

```rust ignore
// give each edge q-->p a color of the tuple (p, q)
let mapped_restricted = aut.map_edge_colors_full(|(q, _e, _c, p)| (p, q))
    // restrict ourselves to state indices strictly smaller than 3
    .restrict_state_indices(|id| id < 3);

// before the assert, no computation on edges or indices has been executed yet
assert!(mapped_restricted.edges_from(0).unwrap().all(|edge| edge.color().0 == 0 && edge.target() != 3));
// we can collect into a fresh TS, but this may mess up indices
let (ts, map )
```

Operations may be computed in full by collecting into a fresh transition system.
In any case, collection is possbile like so
```rust ignore
let collected = mapped_restricted.collect_dts();
// if we had a transition with an initial state, there would also be a pointed variant
let (_ts, _init) = collected.with_initial(0).collect_dts_pointed();

// we may also bypass one construction step and directly collect a certain type of automaton
let mm = mapped_restricted.map_edge_colors(|(a, b)| a + b)
    .collect_mealy();
assert_eq!(mm.map("a"), Some(2));
assert_eq!(mm.map("aa"), Some(4));
assert_eq!(mm.map("babc"), None);
```

For more fine-grained control, it is also possible to straight up chop the transition system up into its [SCCs](https://en.wikipedia.org/wiki/Strongly_connected_component), for which a few different algorithms are available such as a recursive and an iterative implementation of Tarjan's algorithm and an implementation of Kosarajus algorithm. By no means have I done the implementation here alone, there was heavy inspiration especially in the beginning by the code of `petgraph`, thank you so much for your amazing work <3.
```rust ignore
// get direct access to a decomposition into SCCs
let sccs = aut.sccs();//or sccs_kosaraju() or sccs_recursive();
assert_eq!(sccs.first(), &Scc::new(&aut, [0, 1, 2]));

// or build a DAG that encodes this information and gives access to relations between SCCs
let dag = aut.tarjan_dag();
assert_ne!(dag.scc_of(0).unwrap(), dag.scc_of(3).unwrap());

// get set of edges that go between SCCs
let transient_edges: std::collections::HashSet<_> = dag.transient_edges();
assert_eq!(transient_edges.len(), 3);
```

These decompositions are then also what powers some language theoretic operations on automata, for example:
```rust ignore
assert!(aut.accepts(aut.give_word().unwrap()));
assert!(aut.intersection(aut.negation()).is_empty_language());
```

### $\omega$-automata

The automata library also provides some tools for working with [automata over infinite words](https://en.wikipedia.org/wiki/%CE%A9-automaton).
Syntactically, they are the same as a `MealyMachine` (or a `MooreMachine` if we are talking state-based acceptance, which I would rather not, [see here for a discussion](https://theses.hal.science/tel-04314678v1/document#chapter.1473)).
The words we use as input are called *ultimately periodic* and represented as $w=ux^\omega$ ($u$ is the spoke and $v$ is the cycle of $w$).
The library provides data structures, some basic operations, the macro `upw!` and some traits for working with (in)finite words (see `FiniteWord`, `LinearWord` and `OmegaWord` for example).


Such words can then be directly fed into an $\omega$-automaton such as a deterministic parity automaton DPA which has edges labeled with a `usize` color.
For acceptance, we consider the set of transitions (or states if you really must) that are taken infinitely often.
A DPA, for example, accepts a word if the least edge color that is seen infinitely often is even and it rejects otherwise.
Since DPA have nice algorithmic properties and [are able to capture](https://en.wikipedia.org/wiki/%CE%A9-automaton#Expressive_power_of_%CF%89-automata) the full class of $\omega$-regular languages, this library gears mostly towards them.

```rust
use automata::{core::upw, ts::TSBuilder};

let dpa = TSBuilder::without_state_colors()
    .with_transitions([
        (0, 'a', 1, 1),
        (0, 'b', 0, 0),
        (1, 'a', 1, 0),
        (1, 'b', 2, 1),
    ])
    .into_dpa(0);
// the DPA above accepts the ultimately periodic word consisting of only b, i.e. bbbbbb...
assert!(dpa.accepts(upw!("b")));
// but it rejects the word consisting two b followed by infinitely many a
assert!(!dpa.accepts(upw!("bb", "a")))
```

As $\omega$-automata are syntactically the same, we may use the same operations as above on them.
There are already some language-theoretic operations implemented as well.


### [HOA](https://adl.github.io/hoaf/) support

The library provides some basic ability of handling HOA.
Specifically, there exists a parser that lives in the `hoars` subdirectory, which allows inputting deterministic parity automata from HOA.
There are also basic output capabilities in HOA.
An example pipeline can be found in the `oai` binary, under the `todpa` subcommand one can pipe in DPAs, which are parsed, converted into explicitly represented DPAs, before being converted into implicitly represented DPAs and output as HOA again.
By running this pipeline quite a few times (this may be extended for other operations of course), we gain some confidence in implementations in general.
Many thanks go out to the people of [spot](https://spot.lre.epita.fr/) for the excellent tooling they offer.

### Graphviz

Some support for rendering transition systems/automata graphically exists.
This is done through the [graphviz](https://graphviz.org/) library and depends upon the creation of an intermediate _DOT_ description of the underlying graph.

## Installation

For now, there is no stable version on crates.io, add the dependency via git as so:
```ignore
[dependencies]
automata = { git = "https://github.com/leonbohn/automata.git" }
```

### Features
The following features are offered.

| feature name | default value | description |
| ------- | ------- | ------- | 
| `hoa` | `true` | enables input and output of HOA files, using the [hoars](https://github.com/leonbohn/hoars) library |
| `random` | `true` | allows constructing random transition systems with a certain edge probability. |
| `render` | `true` | Moreover, it allows generating SVG representation of the graph without external dependencies. | 
| `implementations` | `false` | Offers some additional implementations of the `TransitionSystem` trait, for example `HashSet` based ones |
| `graphviz` | `false` | through which DOT representation of transition systems/automata can be generated and visualised |

## Development
Any and every help is always welcome.
This is for the most part a personal individual project, therefore very opinionated and in some places maybe even chaotic libarary, sorry for that.

To ensure code quality, the `main` branch may only be modified via pull requests.
The CI is configured that any pull request will run through a set of checks and tests.
Specifically, the formatting is tested, then clippy is run and finally all tests will be run.
To avoid unnecessary runs of the CI, these steps can be run locally before every commit through the `check` script included in the base of the repository.


## Technicalities

In essence, an automaton consists of a transition system together with an acceptance component.
A transition system is simply a finite collection of states which are connected with directed edges.
It can have colors on its states (then each state is assigned precisely one color) as well as colors on its edges (meaning every edge between two states has a color).
If you really want to do a deep dive into the theory behind all this, have a look at either the book "Handbook of Automata Theory" by Jean-Éric Pin (specifically Chapters "Finite Automata" and "$\omega$-automata" in Volume 1). For something that is open access, have a look at [this](https://theses.hal.science/tel-04314678v1/document) or read the description of the formal semantics of $\omega$-automata given [on this page at the bottom](https://adl.github.io/hoaf/).

### Alphabets

The implementation of TS is generic over the alphabet, which can either be simple (i.e. it is just a collection of individual symbols/chars as given implemented in the `CharAlphabet` struct) or propositional (meaning the alphabet consists of a collection of atomic propositions).
With a `CharAlphabet`, words are made up of `char`s and `char`s are what label edges **and** transitions.
In the case of a propositional `HoaAlphabet`, words are made up of `HoaSymbols`, which are what label transitions, but edges are labeled with `HoaExpression`s. You may think of an expression as being a boolean combination of symbols.

We mainly support propositional alphabets from the perspective of verification and interaction with other tools/the HOA format.
Explicit alphabets such as `CharAlphabet`, have a clear advantage conceptually in learning and are inherently simpler to implement.
As such, for smaller experiments and general purpose experimentation, we would suggest using a character based alphabet.

Similar to other libraries dealing with (omega) automata, we distinguish between edges and transitions in a TS. Specifically, an edge is determined by its origin/target state, the color it emits and a guard, which is of the expression type that the alphabet determines. A transition on the other hand is a concretization of an edge, where the guard is a single symbol (also determined by the alphabet). For simple alphabets, expressions and symbols coincide, whereas for propositional alphabets, expressions are formulas (represented as BDDs) over the atomic propositions and symbols are satisfying valuations of expressions.

### Overview

The most important trait is `TransitionSystem`, which provides access to the indices of all states and is capable of returning iterators over the outgoing edges of a state. It also provides a lot of combinators, which allow manipulation of the TS. For example `map_state_color` consumes the TS and relabels the colors on the states through applying a given function. Most combinators consume `self`, returning a new TS, which is mainly to avoid unneccessary cloning of the underlying data structures. If the original TS should continue to exist, call `as_ref` or simply use a reference to the TS.
As each combinator returns an object which again implements `TransitionSystem`, these can easily be chained together without too much overhead. While this is convenient, the applied manipulations are computed on-demand, which may lead to considerable overhead. To circumvent this, it can be beneficial to `collect` the resulting TS into a structure, which then explicitly does all the necessary computations and avoids recomputation at a later point. There are also variants `collect_with_initial`/`collect_ts`, which either take the designated ininital state into account or collect into a specific representation of the TS.

The crate defines some basic building blocks of TS which can easily be manipulated (see `Sproutable`), these are
- `NTS`/`DTS` (the latter is just a thin wrapper around the former). These store edges in a vector, a state contains a pointer to the first edge in this collection and each edge contains pointers to the previous/next one.
- `BTS` which stores transitions in an efficient HashMap

Further traits that are of importance are
- `Pointed` which picks one designated initial state, this is important for deterministic automata
- `Deterministic`, a marker trait that disambiguates between nondeterministic and deterministic TS. As `TransitionSystem` only provides iterators over the outgoing edges, it can be used to deal with nondeterministic TS, that have multiple overlapping edges. By implementing `Deterministic`, we guarantee, that there is always a single unique outgoing transition for each state.
- `Sproutable` enables growing a TS state by state and edge/transition by edge/transition. Naturally, this is only implemented for the basic building blocks, i.e. `BTS`, `DTS` and `NTS`.


### License 

Thanks go out to the maintainers of [`spot`](https://spot.lre.epita.fr/) and [`petgraph`](https://github.com/petgraph/petgraph). Their ideas and their code have been immensely helpful so far. For all the rest, see `LICENSE.md`.
