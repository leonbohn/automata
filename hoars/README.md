# HOArs

A parser for dealing with Hanoi Omega-Automata (HOA) file format, which is described in more detail [here](https://adl.github.io/hoaf/).
At the moment, we can only parse HOA files, support for writing them will be added later.

## Changelog
### 0.2 (240424)
Fix some bugs in the extraction of a label expression for an edge or alias. This no longer defaults to 8 atomic propositions, but builds an abstract expression that is then to be further handled by the consumer downstream.

### 0.1.1 (230414)
Added lots and lots of documentation, some helper methods and introduced a
method for converting label expressions to DNF, which in turn allows to
use them as symbols for an automaton.

### 0.1 (230216)
First release 0.1 version, probably buggy as hell.
