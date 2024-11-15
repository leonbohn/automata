# **co**ngruence-based **l**earning **t**oolkit

This repository contains code that shall one day become a learning toolkit for automata and related formalisms based on (right) congruence relations.
Parts have been stable for a while, others are perpetually unstable.
Help.

Roughly, the repository is split into the following crates:
- `automata-core` which defines core notions for working with alphabets and words. Moreover, it provides utility traits abstracting properties of states and colors, and gives standard mathematical constructions such as dag, set, mapping, etc.
- `automata` introduces transition systems and automata over finite and infinite words, with different acceptance conditions. Moreover, it provides some algorithms such as minimization. Finally, it defines alternative acceptance models such as (families of) right congruences.
- `automata-learning` deals with both passive and active learning of automata. It provides an implementation of L* as well as RPNI.
- `hoars` a parser for the HOA format, which defines an abstract representation of an automaton in HOA format. Currently it only reads such a representation

### What we would additionally like to have
Moar features, of course.
The following come to mind/have already been started/attempted/considered
- `automata-logic` 🚧 this should define various logics that have dep connections to automata
- `python` 🚧 bindings for Python could live here, it might be sensible to expose the automata types to python as well
- `automata-games` 🚧 these things are just so closely related that it would be a crime to not also want to implement stuff there. By using existing graph crates/implementations for once instead of rolling everything ourselves, we might actually have a shot at something usable in a reasonable amount of time.

It might also be a good idea to split the repository up even more, especially the `automata` crate is still beefy.
