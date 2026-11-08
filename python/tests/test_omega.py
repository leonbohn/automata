import pytest

from automata import DBA, CharAlphabet, OmegaWord, PropAlphabet, PropDBA

AB = CharAlphabet("ab")


def inf_a():
    return DBA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)])


def test_omega_word():
    w = OmegaWord("ab", "c")
    assert (w.prefix, w.period) == ("ab", "c")
    assert w == OmegaWord("ab", "c")
    with pytest.raises(ValueError):
        OmegaWord("a", "")
    with pytest.raises(TypeError):
        OmegaWord("a", [[True]])
    with pytest.raises(TypeError):
        OmegaWord(1, 2)


def test_dba():
    d = inf_a()
    assert d.accepts(OmegaWord("bb", "ba")) and not d.accepts(OmegaWord("a", "b"))
    assert not d.is_empty()
    w = d.accepting_word()
    assert d.accepts(w)
    assert sorted(d.edges_from(0)) == sorted([(0, "a", True, 0), (0, "b", False, 0)])
    assert (d.num_states, d.num_edges) == (1, 2)
    never = DBA(AB, 1, 0, [(0, "a", False, 0), (0, "b", False, 0)])
    assert never.is_empty() and never.accepting_word() is None
    assert never.included_in(d) and not d.included_in(never)
    assert d.inclusion_counterexample(never) is not None
    assert d.equivalent_to(inf_a()) and d.equivalence_counterexample(inf_a()) is None


def test_wrong_kind_of_word():
    with pytest.raises(TypeError):
        inf_a().accepts(OmegaWord([[True]], [[False]]))


def test_prop_dba():
    a = PropAlphabet(["p"])
    d = PropDBA(a, 1, 0, [(0, [True], True, 0), (0, [False], False, 0)])
    assert d.accepts(OmegaWord([[False]], [[True], [False]]))
    assert not d.accepts(OmegaWord([[True]], [[False]]))
    w = d.accepting_word()
    assert d.accepts(w)
    with pytest.raises(ValueError):
        d.accepts(OmegaWord([[True, True]], [[True]]))


def test_sccs():
    d = DBA(AB, 3, 0, [(0, "a", False, 1), (0, "b", False, 0), (1, "a", True, 1), (1, "b", True, 2), (2, "a", False, 2), (2, "b", False, 2)])
    assert sorted(map(sorted, d.sccs())) == [[0], [1], [2]]
    assert sorted(map(sorted, inf_a().sccs())) == [[0]]
