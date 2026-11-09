# automatars

Python bindings for the Rust crate [`automata`](https://github.com/leonbohn/automata): transition
systems and automata over finite and infinite words. Install with `pip install automatars`;
the module is imported as `automata`.

```python
from automata import CharAlphabet, DFA, DBA, OmegaWord

ab = CharAlphabet("ab")

# words with an even number of a's: DFA(alphabet, num_states, initial, accepting, edges)
even_a = DFA(ab, 2, 0, [0], [(0, "a", 1), (0, "b", 0), (1, "a", 0), (1, "b", 1)])
assert even_a.accepts("abba")
assert even_a.complement().accepting_word() == "a"
assert even_a.minimize().num_states == 2

# infinitely many a's: DBA edges carry a color, `True` means accepting
inf_a = DBA(ab, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)])
assert inf_a.accepts(OmegaWord("bb", "ab"))      # bb (ab)^ω
assert not inf_a.accepts(OmegaWord("a", "b"))    # a b^ω
```

## Classes

Every automaton class exists twice: over a `CharAlphabet` (symbols are characters, words are
strings) and over a `PropAlphabet` (a symbol is a valuation of the atomic propositions, given as a
list of booleans; the class name has the prefix `Prop`, e.g. `PropDBA`). HOA files use propositional
alphabets.

| | finite words | infinite words |
| --- | --- | --- |
| deterministic | `DFA` | `DBA`, `DCA`, `DPA` (min even), `DPAMaxEven`, `DPAMinOdd`, `DPAMaxOdd`, `DRA`, `DSA`, `DMA` |
| nondeterministic | `NFA` | `NBA`, `NCA`, `NPA` (min even) |
| output | `MooreMachine`, `MealyMachine` | |

All of them have `accepts`/`output`, `num_states`, `num_edges`, `initial`, `states()`,
`edges_from(q)` and `sccs()`. Language problems (`is_empty`, `accepting_word`, `included_in`,
`inclusion_counterexample`, `equivalent_to`, `equivalence_counterexample`) are available where the
Rust crate decides them. Automata are immutable; operations return new automata. Lazy adapters of
the Rust API are not exposed.

The three other parity conditions are classes of their own (the color of an edge is a number
from 0 to 255 in all of them). `to_min_even()` gives the equivalent `DPA`, `complement()` the
automaton with the dual condition (`DPAMaxEven` and `DPAMaxOdd` are complements of each other, the
complement of `DPAMinOdd` is a `DPA`), `is_empty()` and `accepting_word()` work on `to_min_even()`.
`DSA` is the Streett automaton with the constructor of `DRA`: `DSA(alphabet, num_states, initial,
edges, pairs)` accepts if for every pair `(fin, inf)` no color of `fin` or some color of `inf`
occurs infinitely often.

Automata can also be built step by step with `DFABuilder` (and the builders in `automata.builders`).

## HOA

`to_hoa()` writes `DBA`, `DCA`, the four parity classes, `DRA`, `DSA`, `NBA`, `NCA` and `NPA`
(and their `Prop` variants); characters become propositions. `from_hoa(text)` and
`automata.parse_hoa(text)` need propositional alphabets, so only the `Prop` classes have
`from_hoa`:

| class | reads |
| --- | --- |
| `PropDBA`, `PropDCA` | deterministic Büchi, co-Büchi |
| `PropDPA` | every parity kind, Büchi and co-Büchi, converted to min even (`NotImplementedError` for Rabin/Streett) |
| `PropDPAMaxEven`, `PropDPAMinOdd`, `PropDPAMaxOdd` | exactly their own parity kind, the colors are kept |
| `PropDRA`, `PropDSA` | deterministic Rabin, Streett |
| `PropNBA`, `PropNCA`, `PropNPA` | also deterministic automata; `PropNPA` only min even |

`parse_hoa` returns the most specific class (`PropDPAMaxEven` for `parity max even`, `PropNCA` for
a nondeterministic co-Büchi automaton, ...); nondeterministic Rabin/Streett automata, generalized
conditions and nondeterministic parity automata other than min even raise
`NotImplementedError`. An edge of a HOA automaton belongs to a *set* of acceptance sets, an edge of
a `DRA`/`DSA` has one color. `PropDRA.from_hoa` and `PropDSA.from_hoa` therefore number the
distinct sets of acceptance sets on the edges `0, 1, ...` in the order of their first occurrence
(the empty set is a color, more than 256 different sets are a `HoaError`) and rewrite the pairs:
a color is in `fin` (`inf`) if its set meets a `fin` (`inf`) set of the pair. `to_hoa()` of a `DRA`
or `DSA` can only be read back if its pairs are `([0], [1])`, `([2], [3])`, ... .

## Errors

Everything raised by the library derives from `automata.Error`: `HoaError`, `PropAlphabetError`,
`BuilderError`, `AcceptanceError` and `NotPeriodicError`. Operations the crate does not implement
raise `NotImplementedError`. Invalid arguments (unknown states or symbols) raise `ValueError`,
`TypeError` or `IndexError`.

## Development

```shell
cd python
python -m venv .venv && . .venv/bin/activate
pip install maturin pytest
maturin develop
python -m pytest            # includes the doctests of the classes
cargo run --bin stub_gen    # regenerates automata/_automata/__init__.pyi
```
