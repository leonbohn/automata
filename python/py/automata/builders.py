"""Step by step construction of deterministic omega automata.

There is one builder per class of automata (``DBABuilder`` for ``DBA``, ``PropDBABuilder`` for
``PropDBA``, ...). All of them are used the same way: add states, add edges, set the initial
state and call ``build``. Everything is checked as soon as it is added, errors are ``ValueError``
(unknown states, symbols or colors that are out of range) or ``TypeError`` (values of the wrong
type).
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from typing import Any, ClassVar, Generic, TypeVar

from automata._automata import (
    DBA,
    DCA,
    DMA,
    DPA,
    DRA,
    CharAlphabet,
    PropAlphabet,
    PropDBA,
    PropDCA,
    PropDMA,
    PropDPA,
    PropDRA,
)

__all__ = [
    "DBABuilder",
    "DCABuilder",
    "DMABuilder",
    "DPABuilder",
    "DRABuilder",
    "PropDBABuilder",
    "PropDCABuilder",
    "PropDMABuilder",
    "PropDPABuilder",
    "PropDRABuilder",
]

A = TypeVar("A", CharAlphabet, PropAlphabet)
R = TypeVar("R")
# a symbol is a character for a `CharAlphabet` and a sequence of booleans for a `PropAlphabet`
Symbol = str | Sequence[bool]


def _color(value: object, boolean: bool) -> bool | int:
    """Checks an edge color: a bool for Büchi and co-Büchi, an integer in ``0..=255`` otherwise."""
    if boolean:
        if not isinstance(value, bool):
            raise TypeError(f"the color has to be a bool, got {value!r}")
        return value
    if not isinstance(value, int):
        raise TypeError(f"the color has to be an integer, got {value!r}")
    if not 0 <= value <= 255:
        raise ValueError(f"the color {value} is not in 0..=255")
    return int(value)


def _colors(values: Iterable[object]) -> list[int]:
    return [_color(c, False) for c in values]


class _Builder(Generic[A, R]):
    """Common part of all builders; subclasses fix the class that is built."""

    _target: ClassVar[Any]
    _alphabet_type: ClassVar[type]
    _boolean_colors: ClassVar[bool]

    def __init__(self, alphabet: A) -> None:
        if not isinstance(alphabet, self._alphabet_type):
            raise TypeError(f"expected a {self._alphabet_type.__name__}, got {alphabet!r}")
        self._alphabet = alphabet
        self._num_states = 0
        self._initial: int | None = None
        self._edges: list[tuple[int, Any, bool | int, int]] = []

    @property
    def num_states(self) -> int:
        """The number of states added so far."""
        return self._num_states

    def add_state(self) -> int:
        """Adds a state and returns its number (``0, 1, 2, ...``)."""
        self._num_states += 1
        return self._num_states - 1

    def _state(self, state: int) -> int:
        if not isinstance(state, int) or isinstance(state, bool):
            raise TypeError(f"a state is an integer, got {state!r}")
        if not 0 <= state < self._num_states:
            raise ValueError(f"state {state} does not exist, there are {self._num_states} states")
        return state

    def _symbol(self, symbol: Symbol) -> Symbol:
        if isinstance(self._alphabet, CharAlphabet):
            if not isinstance(symbol, str):
                raise TypeError(f"a symbol is a single character, got {symbol!r}")
            if len(symbol) != 1 or symbol not in self._alphabet.symbols:
                raise ValueError(f"{symbol!r} is not in the alphabet")
            return symbol
        if isinstance(symbol, str) or not isinstance(symbol, Sequence):
            raise TypeError(f"a symbol is a sequence of booleans, got {symbol!r}")
        if not all(isinstance(b, bool) for b in symbol):
            raise TypeError(f"a symbol is a sequence of booleans, got {symbol!r}")
        if len(symbol) != len(self._alphabet.aps):
            raise ValueError(f"a symbol needs {len(self._alphabet.aps)} booleans, got {len(symbol)}")
        return list(symbol)

    def add_edge(self, source: int, symbol: Symbol, color: bool | int, target: int) -> None:
        """Adds an edge between existing states.

        An edge with the same source and symbol that was added earlier is replaced.
        """
        edge = (self._state(source), self._symbol(symbol), _color(color, self._boolean_colors), self._state(target))
        self._edges.append(edge)

    def set_initial(self, state: int) -> None:
        """Sets the initial state, which has to exist."""
        self._initial = self._state(state)

    def _extra(self) -> tuple[Any, ...]:
        """The arguments of the constructor that follow the edges."""
        return ()

    def build(self) -> R:
        """Creates the automaton. Raises ``ValueError`` if no initial state was set.

        The builder can be used further.
        """
        if self._initial is None:
            raise ValueError("no initial state set")
        return self._target(self._alphabet, self._num_states, self._initial, list(self._edges), *self._extra())


class _RabinBuilder(_Builder[A, R]):
    _boolean_colors = False

    def __init__(self, alphabet: A, pairs: Iterable[tuple[Iterable[int], Iterable[int]]]) -> None:
        super().__init__(alphabet)
        self._pairs = [(_colors(fin), _colors(inf)) for fin, inf in pairs]

    def _extra(self) -> tuple[Any, ...]:
        return (list(self._pairs),)


class _MullerBuilder(_Builder[A, R]):
    _boolean_colors = False

    def __init__(self, alphabet: A, sets: Iterable[Iterable[int]]) -> None:
        super().__init__(alphabet)
        self._sets = [_colors(s) for s in sets]

    def _extra(self) -> tuple[Any, ...]:
        return (list(self._sets),)


class DBABuilder(_Builder[CharAlphabet, DBA]):
    """Builds a ``DBA`` (edge colors are bools).

    >>> b = DBABuilder(CharAlphabet("ab"))
    >>> q = b.add_state()
    >>> b.add_edge(q, "a", True, q)
    >>> b.add_edge(q, "b", False, q)
    >>> b.set_initial(q)
    >>> b.build().accepts(OmegaWord("b", "ab"))
    True
    """

    _target = DBA
    _alphabet_type = CharAlphabet
    _boolean_colors = True


class PropDBABuilder(_Builder[PropAlphabet, PropDBA]):
    """Builds a ``PropDBA``, see ``DBABuilder``; symbols are sequences of booleans."""

    _target = PropDBA
    _alphabet_type = PropAlphabet
    _boolean_colors = True


class DCABuilder(_Builder[CharAlphabet, DCA]):
    """Builds a ``DCA`` (edge colors are bools), see ``DBABuilder``."""

    _target = DCA
    _alphabet_type = CharAlphabet
    _boolean_colors = True


class PropDCABuilder(_Builder[PropAlphabet, PropDCA]):
    """Builds a ``PropDCA``, see ``DCABuilder``."""

    _target = PropDCA
    _alphabet_type = PropAlphabet
    _boolean_colors = True


class DPABuilder(_Builder[CharAlphabet, DPA]):
    """Builds a ``DPA`` (edge colors are integers in ``0..=255``).

    >>> b = DPABuilder(CharAlphabet("ab"))
    >>> q = b.add_state()
    >>> b.add_edge(q, "a", 1, q)
    >>> b.add_edge(q, "b", 0, q)
    >>> b.set_initial(q)
    >>> b.build().accepts(OmegaWord("a", "ab"))
    True
    """

    _target = DPA
    _alphabet_type = CharAlphabet
    _boolean_colors = False


class PropDPABuilder(_Builder[PropAlphabet, PropDPA]):
    """Builds a ``PropDPA``, see ``DPABuilder``."""

    _target = PropDPA
    _alphabet_type = PropAlphabet
    _boolean_colors = False


class DRABuilder(_RabinBuilder[CharAlphabet, DRA]):
    """Builds a ``DRA`` from the alphabet and the Rabin pairs ``(fin, inf)`` of colors.

    >>> b = DRABuilder(CharAlphabet("ab"), [([], [1])])
    >>> q = b.add_state()
    >>> b.add_edge(q, "a", 0, q)
    >>> b.add_edge(q, "b", 1, q)
    >>> b.set_initial(q)
    >>> b.build().accepts(OmegaWord("", "ab"))
    True
    """

    _target = DRA
    _alphabet_type = CharAlphabet


class PropDRABuilder(_RabinBuilder[PropAlphabet, PropDRA]):
    """Builds a ``PropDRA``, see ``DRABuilder``."""

    _target = PropDRA
    _alphabet_type = PropAlphabet


class DMABuilder(_MullerBuilder[CharAlphabet, DMA]):
    """Builds a ``DMA`` from the alphabet and the accepting sets of colors.

    >>> b = DMABuilder(CharAlphabet("ab"), [[1]])
    >>> q = b.add_state()
    >>> b.add_edge(q, "a", 0, q)
    >>> b.add_edge(q, "b", 1, q)
    >>> b.set_initial(q)
    >>> b.build().accepts(OmegaWord("", "ab"))
    False
    """

    _target = DMA
    _alphabet_type = CharAlphabet


class PropDMABuilder(_MullerBuilder[PropAlphabet, PropDMA]):
    """Builds a ``PropDMA``, see ``DMABuilder``."""

    _target = PropDMA
    _alphabet_type = PropAlphabet
