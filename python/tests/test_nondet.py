import pytest

from automata import (
    DBA,
    DFA,
    NBA,
    NCW,
    NFA,
    NPA,
    CharAlphabet,
    OmegaWord,
    PropAlphabet,
    PropDBA,
    PropDFA,
    PropNBA,
    PropNCW,
    PropNFA,
    PropNPA,
)

AB = CharAlphabet("ab")
SECOND_LAST_A = [(0, "a", 0), (0, "b", 0), (0, "a", 1), (1, "a", 2), (1, "b", 2)]


def second_last_a():
    return NFA(AB, 3, 0, [2], SECOND_LAST_A)


def test_nfa_accepts_and_structure():
    n = second_last_a()
    assert n.accepts("bab") and n.accepts("aa") and not n.accepts("abb") and not n.accepts("")
    assert (n.num_states, n.num_edges, n.initial) == (3, 5, 0)
    assert n.accepting_states() == [2] and n.is_accepting(2) and not n.is_accepting(0)
    assert sorted(n.edges_from(0)) == [(0, "a", 0), (0, "a", 1), (0, "b", 0)]
    assert n.accepts("zz") is False  # symbols outside of the alphabet leave the automaton
    assert "NFA" in repr(n)


def test_nfa_errors():
    with pytest.raises(ValueError):
        NFA(AB, 1, 1, [], [])
    with pytest.raises(ValueError):
        NFA(AB, 1, 0, [3], [])
    with pytest.raises(ValueError):
        NFA(AB, 1, 0, [], [(0, "c", 0)])
    with pytest.raises(ValueError):
        NFA(AB, 1, 0, [], [(0, "a", 4)])
    with pytest.raises(IndexError):
        second_last_a().is_accepting(7)
    with pytest.raises(IndexError):
        second_last_a().edges_from(7)


def test_nfa_emptiness():
    n = second_last_a()
    assert not n.is_empty() and n.accepting_word() == "aa"
    e = NFA(AB, 2, 0, [1], [(0, "a", 0)])
    assert e.is_empty() and e.accepting_word() is None


def test_nfa_determinize_and_comparisons():
    n = second_last_a()
    d = n.determinize()
    assert isinstance(d, DFA)
    assert d.minimize().num_states == 4
    for w in ["", "a", "ab", "aab", "bab", "abb", "bbaa"]:
        assert d.accepts(w) == n.accepts(w)
    assert NFA.from_dfa(d).equivalent_to(n)
    assert n.equivalence_counterexample(NFA.from_dfa(d)) is None
    # a superset: every word that ends in a
    ends_a = NFA(AB, 2, 0, [1], [(0, "a", 1), (0, "b", 0), (1, "a", 1), (1, "b", 0)])
    assert n.included_in(ends_a) is False
    cex = n.inclusion_counterexample(ends_a)
    assert n.accepts(cex) and not ends_a.accepts(cex)
    assert ends_a.inclusion_counterexample(n) is not None
    other = n.equivalence_counterexample(ends_a)
    assert n.accepts(other) != ends_a.accepts(other)
    assert not n.equivalent_to(ends_a)
    with pytest.raises(ValueError):
        n.included_in(NFA(CharAlphabet("abc"), 1, 0, [0], []))
    with pytest.raises(ValueError):
        n.equivalent_to(NFA(CharAlphabet("abc"), 1, 0, [0], []))


def test_nfa_from_dfa():
    d = DFA(AB, 2, 0, [0], [(0, "a", 1), (0, "b", 0), (1, "a", 0), (1, "b", 1)])
    n = NFA.from_dfa(d)
    assert isinstance(n, NFA) and (n.num_states, n.num_edges) == (2, 4)
    assert n.accepts("abba") and not n.accepts("a")
    assert n.accepting_states() == [0]


def test_prop_nfa():
    a = PropAlphabet(["p"])
    n = PropNFA(a, 2, 0, [1], [(0, [True], 0), (0, [False], 0), (0, [True], 1)])
    assert n.accepts([[False], [True]]) and not n.accepts([[True], [False]])
    assert n.accepting_word() == [[True]]
    d = n.determinize()
    assert isinstance(d, PropDFA) and d.accepts([[False], [True]])
    assert PropNFA.from_dfa(d).equivalent_to(n)
    with pytest.raises(ValueError):
        PropNFA(a, 1, 0, [], [(0, [True, True], 0)])


def nba_fin_a():
    return NBA(AB, 2, 0, [(0, "a", False, 0), (0, "b", False, 0), (0, "b", False, 1), (1, "b", True, 1)])


def test_nba():
    n = nba_fin_a()
    assert n.accepts(OmegaWord("ab", "b")) and not n.accepts(OmegaWord("", "ab"))
    assert not n.is_empty()
    w = n.accepting_word()
    assert n.accepts(w)
    assert (n.num_states, n.num_edges) == (2, 4)
    assert sorted(n.edges_from(0)) == [(0, "a", False, 0), (0, "b", False, 0), (0, "b", False, 1)]
    assert NBA(AB, 1, 0, [(0, "a", False, 0)]).is_empty()
    assert NBA(AB, 1, 0, [(0, "a", False, 0)]).accepting_word() is None


def test_nba_errors():
    with pytest.raises(ValueError):
        NBA(AB, 1, 0, [(0, "c", True, 0)])
    with pytest.raises(ValueError):
        NBA(AB, 1, 0, [(0, "a", True, 1)])
    with pytest.raises(TypeError):
        nba_fin_a().accepts(OmegaWord([[True]], [[True]]))
    with pytest.raises(IndexError):
        nba_fin_a().edges_from(2)


def test_nba_from_dba():
    d = DBA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)])
    n = NBA.from_dba(d)
    assert isinstance(n, NBA) and (n.num_states, n.num_edges) == (1, 2)
    for w in [OmegaWord("", "a"), OmegaWord("a", "b"), OmegaWord("bb", "ba")]:
        assert n.accepts(w) == d.accepts(w)
    pd = PropDBA(PropAlphabet(["p"]), 1, 0, [(0, [True], True, 0)])
    assert PropNBA.from_dba(pd).accepts(OmegaWord([[True]], [[True]]))


def test_ncw():
    n = NCW(AB, 2, 0, [(0, "a", True, 0), (0, "b", True, 0), (0, "b", False, 1), (1, "b", False, 1)])
    assert n.accepts(OmegaWord("ab", "b")) and not n.accepts(OmegaWord("", "ab"))
    assert not n.is_empty() and n.accepts(n.accepting_word())
    assert NCW(AB, 1, 0, [(0, "a", True, 0)]).is_empty()


def test_npa():
    n = NPA(AB, 2, 0, [(0, "a", 1, 0), (0, "b", 1, 0), (0, "b", 1, 1), (1, "b", 0, 1)])
    assert n.accepts(OmegaWord("ab", "b")) and not n.accepts(OmegaWord("", "ab"))
    assert not n.is_empty() and n.accepts(n.accepting_word())
    assert NPA(AB, 1, 0, [(0, "a", 1, 0)]).is_empty()
    with pytest.raises(OverflowError):
        NPA(AB, 1, 0, [(0, "a", 300, 0)])
    with pytest.raises(OverflowError):
        NPA(AB, 1, 0, [(0, "a", -1, 0)])


def test_prop_omega():
    a = PropAlphabet(["p"])
    t, f = [True], [False]
    edges = [(0, f, False, 0), (0, t, False, 0), (0, t, True, 1), (1, t, True, 1)]
    for cls, colors in [(PropNBA, (False, True)), (PropNCW, (True, False)), (PropNPA, (1, 0))]:
        n = cls(a, 2, 0, [(s, x, colors[int(c)], q) for s, x, c, q in edges])
        assert n.accepts(OmegaWord([f], [t])), cls
        assert not n.accepts(OmegaWord([], [f, t])), cls
        assert not n.is_empty() and n.accepts(n.accepting_word()), cls
        with pytest.raises(ValueError):
            cls(a, 1, 0, [(0, [True, True], colors[0], 0)])
