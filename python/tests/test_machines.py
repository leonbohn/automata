import pytest

from automata import (
    DFA,
    CharAlphabet,
    MealyMachine,
    MooreMachine,
    PropAlphabet,
    PropDFA,
    PropMealyMachine,
    PropMooreMachine,
)

AB = CharAlphabet("ab")
# counts a's, saturating at 2
COUNT = [(0, "a", 1), (0, "b", 0), (1, "a", 2), (1, "b", 0), (2, "a", 2), (2, "b", 2)]


def count_a():
    return MooreMachine(AB, [0, 1, 2], 0, COUNT)


def test_moore_output():
    m = count_a()
    assert [m.output(w) for w in ["", "a", "aa", "aab", "ab"]] == [0, 1, 2, 2, 0]
    assert m.output("c") is None  # leaves the alphabet
    assert m.state_output(1) == 1
    with pytest.raises(IndexError):
        m.state_output(3)
    assert (m.num_states, m.num_edges, m.initial) == (3, 6, 0)
    assert m.color_range() == [0, 1, 2]


def test_moore_missing_edge():
    m = MooreMachine(AB, [5, 7], 0, [(0, "a", 1)])
    assert m.output("a") == 7 and m.output("b") is None and m.output("aa") is None


def test_moore_invalid_construction():
    with pytest.raises(ValueError):
        MooreMachine(AB, [], 0, [])
    with pytest.raises(ValueError):
        MooreMachine(AB, [0], 1, [])
    with pytest.raises(ValueError):
        MooreMachine(AB, [0], 0, [(0, "c", 0)])
    with pytest.raises(ValueError):
        MooreMachine(AB, [0], 0, [(0, "a", 1)])
    with pytest.raises(OverflowError):
        MooreMachine(AB, [256], 0, [])


def test_moore_dfas():
    m = count_a()
    dfas = m.decompose_dfa()
    assert len(dfas) == 3 and all(isinstance(d, DFA) for d in dfas)
    assert [d.accepts("a") for d in dfas] == [False, True, True]
    # outputs <= 2 are everything
    assert dfas[2].equivalent_to(m.color_or_below_dfa(2)) and dfas[2].accepting_word() == ""
    assert m.color_or_below_dfa(0).accepting_word() == ""
    assert m.color_or_below_dfa(0).accepts("b") and not m.color_or_below_dfa(0).accepts("a")


def test_moore_bisimilar_and_minimize():
    m = count_a()
    # an equivalent machine with duplicated states 0 and 3
    big = MooreMachine(
        AB,
        [0, 1, 2, 0],
        0,
        [(0, "a", 1), (0, "b", 3), (1, "a", 2), (1, "b", 3), (2, "a", 2), (2, "b", 2), (3, "a", 1), (3, "b", 0)],
    )
    assert m.bisimilar(big) and m.witness_non_bisimilarity(big) is None
    small = big.minimize()
    assert small.num_states == 3 and small.bisimilar(m)
    other = MooreMachine(AB, [0, 1, 1], 0, COUNT)
    assert not m.bisimilar(other)
    assert m.witness_non_bisimilarity(other) == "aa"
    with pytest.raises(ValueError):
        m.bisimilar(MooreMachine(CharAlphabet("abc"), [0], 0, []))


def test_moore_to_mealy():
    mealy = count_a().push_colors_to_outgoing_edges()
    assert isinstance(mealy, MealyMachine)
    assert mealy.output("a") == 0 and mealy.output("aa") == 1 and mealy.output("aaa") == 2


def test_prop_moore():
    a = PropAlphabet(["p"])
    m = PropMooreMachine(a, [0, 1], 0, [(0, [True], 1), (0, [False], 0), (1, [True], 1), (1, [False], 0)])
    assert m.output([[True], [True]]) == 1 and m.output([[True], [False]]) == 0 and m.output([]) == 0
    assert m.color_range() == [0, 1]
    assert all(isinstance(d, PropDFA) for d in m.decompose_dfa())
    assert m.minimize().num_states == 2 and m.bisimilar(m)
    assert m.witness_non_bisimilarity(PropMooreMachine(a, [0, 0], 0, [(0, [True], 1), (0, [False], 0), (1, [True], 1), (1, [False], 0)])) == [[True]]
    with pytest.raises(ValueError):
        PropMooreMachine(a, [0], 0, [(0, [True, False], 0)])
    assert isinstance(m.push_colors_to_outgoing_edges(), PropMealyMachine)


# output: parity of the number of a's so far
MEALY = [(0, "a", 1, 1), (0, "b", 0, 0), (1, "a", 0, 0), (1, "b", 1, 1)]


def test_mealy_output():
    m = MealyMachine(AB, 2, 0, MEALY)
    assert m.output("") is None  # no edge taken
    assert [m.output(w) for w in ["a", "ab", "aa", "aba"]] == [1, 1, 0, 0]
    assert m.output("c") is None
    assert sorted(m.edges_from(0)) == [(0, "a", 1, 1), (0, "b", 0, 0)]
    assert m.color_range() == [0, 1]
    assert (m.num_states, m.num_edges) == (2, 4)


def test_mealy_missing_edge_and_invalid():
    m = MealyMachine(AB, 1, 0, [(0, "a", 3, 0)])
    assert m.output("a") == 3 and m.output("ab") is None
    with pytest.raises(ValueError):
        MealyMachine(AB, 0, 0, [])
    with pytest.raises(ValueError):
        MealyMachine(AB, 1, 0, [(0, "a", 1, 2)])
    with pytest.raises(ValueError):
        MealyMachine(AB, 1, 0, [(0, "z", 1, 0)])
    with pytest.raises(OverflowError):
        MealyMachine(AB, 1, 0, [(0, "a", 256, 0)])


def test_mealy_equivalence_and_minimize():
    m = MealyMachine(AB, 2, 0, MEALY)
    # the same machine with two copies of state 0
    big = MealyMachine(AB, 3, 0, [(0, "a", 1, 1), (0, "b", 0, 2), (1, "a", 0, 0), (1, "b", 1, 1), (2, "a", 1, 1), (2, "b", 0, 2)])
    assert m.bisimilar(big) and big.bisimilar(m)
    assert m.witness_inequivalence(big) is None
    small = big.minimize()
    assert small.num_states == 2 and small.bisimilar(m)
    other = MealyMachine(AB, 2, 0, [(0, "a", 1, 1), (0, "b", 0, 0), (1, "a", 0, 0), (1, "b", 0, 1)])
    assert not m.bisimilar(other)
    assert m.witness_inequivalence(other) == "ab"
    assert m.witness_restricted_inequivalence(other) == "ab"
    # a missing edge in `self` is not a difference seen from `self`, but from the other side
    partial = MealyMachine(AB, 2, 0, [(0, "a", 1, 1), (1, "a", 0, 0)])
    assert partial.witness_restricted_inequivalence(m) is None
    assert m.witness_restricted_inequivalence(partial) == "b"
    assert partial.witness_inequivalence(m) == "b" and not partial.bisimilar(m)
    with pytest.raises(ValueError):
        m.bisimilar(MealyMachine(CharAlphabet("abc"), 1, 0, []))


def test_prop_mealy():
    a = PropAlphabet(["p"])
    m = PropMealyMachine(a, 1, 0, [(0, [True], 1, 0), (0, [False], 0, 0)])
    assert m.output([]) is None and m.output([[False], [True]]) == 1
    assert m.color_range() == [0, 1]
    assert m.minimize().num_states == 1 and m.bisimilar(m)
    other = PropMealyMachine(a, 1, 0, [(0, [True], 1, 0), (0, [False], 1, 0)])
    assert m.witness_inequivalence(other) == [[False]]
