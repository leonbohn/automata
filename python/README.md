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
| deterministic | `DFA` | `DBA`, `DCW`, `DPA` (min-even), `DRA`, `DMA` |
| nondeterministic | `NFA` | `NBA`, `NCW`, `NPA` (min-even) |
| output | `MooreMachine`, `MealyMachine` | |

All of them have `accepts`/`output`, `num_states`, `num_edges`, `initial`, `states()`,
`edges_from(q)` and `sccs()`. Language problems (`is_empty`, `accepting_word`, `included_in`,
`inclusion_counterexample`, `equivalent_to`, `equivalence_counterexample`) are available where the
Rust crate decides them. Automata are immutable; operations return new automata. Lazy adapters of
the Rust API are not exposed.

Automata can also be built step by step with `DFABuilder` (and the builders in `automata.builders`).

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
