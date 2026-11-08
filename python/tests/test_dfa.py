import doctest

import pytest

import automata
from automata import DFA, CharAlphabet, DFABuilder, PropAlphabet, PropDFA, PropDFABuilder

AB = CharAlphabet("ab")
EVEN_A = [(0, "a", 1), (0, "b", 0), (1, "a", 0), (1, "b", 1)]


def even_a():
    return DFA(AB, 2, 0, [0], EVEN_A)


def test_doctests():
    finder = doctest.DocTestFinder()
    runner = doctest.DocTestRunner()
    for cls in (CharAlphabet, PropAlphabet, DFA, PropDFA, DFABuilder, PropDFABuilder):
        for t in finder.find(cls, cls.__name__, globs=dict(vars(automata))):
            runner.run(t)
    results = runner.summarize(verbose=False)
    assert results.attempted >= 20 and results.failed == 0


def test_alphabets():
    assert CharAlphabet("ba") == CharAlphabet("abb")
    assert CharAlphabet("ba").symbols == "ab"
    assert len(PropAlphabet(["p", "q", "r"])) == 8
    with pytest.raises(automata.PropAlphabetError):
        PropAlphabet([])


def test_accepts():
    d = even_a()
    assert d.accepts("") and d.accepts("abba") and not d.accepts("a")
    assert not d.accepts("ac")  # leaves the alphabet


def test_structure():
    d = even_a()
    assert (d.num_states, d.num_edges, d.initial) == (2, 4, 0)
    assert d.states() == [0, 1]
    assert sorted(d.edges_from(0)) == [(0, "a", 1), (0, "b", 0)]
    assert d.is_accepting(0) and not d.is_accepting(1)
    assert d.alphabet == AB
    with pytest.raises(IndexError):
        d.edges_from(2)


def test_invalid_construction():
    with pytest.raises(ValueError):
        DFA(AB, 1, 1, [], [])
    with pytest.raises(ValueError):
        DFA(AB, 2, 0, [], [(0, "c", 1)])
    with pytest.raises(ValueError):
        DFA(AB, 2, 0, [], [(0, "a", 5)])


def test_later_edge_replaces_earlier():
    d = DFA(AB, 2, 0, [1], [(0, "a", 0), (0, "a", 1)])
    assert d.num_edges == 1 and d.accepts("a")


def test_prop_dfa():
    a = PropAlphabet(["p", "q"])
    edges = [(0, [x, y], 1 if x and y else 0) for x in (False, True) for y in (False, True)]
    edges += [(1, [x, y], 1) for x in (False, True) for y in (False, True)]
    d = PropDFA(a, 2, 0, [1], edges)
    assert d.accepts([[False, False], [True, True]])
    assert not d.accepts([[False, True]])
    assert d.num_edges == 8
    assert d.alphabet.aps == ["p", "q"]
    with pytest.raises(ValueError):
        d.accepts([[True]])


def test_builder():
    b = DFABuilder(AB)
    q0, q1 = b.add_state(True), b.add_state()
    for e in EVEN_A:
        b.add_edge(*e)
    with pytest.raises(ValueError):
        b.build()  # no initial state
    b.set_initial(q0)
    d = b.build()
    assert d.accepts("abba") and not d.accepts("a")
    assert (d.num_states, d.num_edges) == (2, 4)
    b.set_accepting(q1)  # the builder stays usable, built DFAs are unaffected
    assert b.build().is_accepting(1) and not d.is_accepting(1)


def test_builder_validation():
    b = DFABuilder(AB)
    b.add_state()
    with pytest.raises(ValueError):
        b.add_edge(0, "a", 1)
    with pytest.raises(ValueError):
        b.add_edge(0, "c", 0)
    with pytest.raises(ValueError):
        b.set_initial(1)


def test_prop_builder():
    b = PropDFABuilder(PropAlphabet(["p"]))
    q = b.add_state(True)
    b.add_edge(q, [True], q)
    b.set_initial(q)
    assert b.build().accepts([[True]] * 3)
    with pytest.raises(ValueError):
        b.add_edge(q, [True, False], q)
