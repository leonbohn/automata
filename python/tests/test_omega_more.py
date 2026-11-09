import pytest

import automata
from automata import (
    DCA,
    DMA,
    DPA,
    DRA,
    CharAlphabet,
    DCABuilder,
    DMABuilder,
    DPABuilder,
    DRABuilder,
    OmegaWord,
    PropAlphabet,
    PropDCA,
    PropDCABuilder,
    PropDMA,
    PropDMABuilder,
    PropDPA,
    PropDPABuilder,
    PropDRA,
    PropDRABuilder,
)

AB = CharAlphabet("ab")
P = PropAlphabet(["p"])
T, F = [True], [False]
TWO_STATE = [(0, "a", 0, 0), (0, "b", 1, 1), (1, "a", 0, 0), (1, "b", 1, 1)]  # color 1 = last letter was b


def w(prefix, period):
    return OmegaWord(prefix, period)


def test_dca():
    d = DCA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)])
    assert d.accepts(w("aa", "b")) and not d.accepts(w("", "ab"))
    assert d.accepting_word() is not None and d.accepts(d.accepting_word())
    assert DCA(AB, 1, 0, [(0, "a", True, 0), (0, "b", True, 0)]).is_empty()
    assert (d.num_states, d.num_edges) == (1, 2)
    assert not hasattr(d, "complement")


def test_prop_dca():
    d = PropDCA(P, 1, 0, [(0, T, True, 0), (0, F, False, 0)])
    assert d.accepts(w([T], [F])) and not d.accepts(w([], [T, F]))
    with pytest.raises(ValueError):
        PropDCA(P, 1, 0, [(0, [True, True], True, 0)])
    with pytest.raises(TypeError):
        d.accepts(w("a", "b"))


INF_B = [(0, "a", 1, 0), (0, "b", 0, 0)]


def test_dpa():
    d = DPA(AB, 1, 0, INF_B)
    assert d.accepts(w("a", "ab")) and not d.accepts(w("b", "a"))
    assert not d.is_empty() and d.accepts(d.accepting_word())
    assert d.rejected_word() is not None and not d.accepts(d.rejected_word())
    assert DPA(AB, 1, 0, [(0, "a", 2, 0), (0, "b", 0, 0)]).rejected_word() is None
    assert DPA(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 1, 0)]).is_empty()


def test_dpa_complement_and_normalization():
    d = DPA(AB, 2, 0, [(0, "a", 4, 1), (0, "b", 3, 0), (1, "a", 6, 0), (1, "b", 5, 1)])
    c = d.complement()
    for word in [w("", "a"), w("", "b"), w("a", "ab"), w("b", "aab"), w("", "ba")]:
        assert c.accepts(word) != d.accepts(word)
    assert d.inclusion_counterexample(c) is not None or d.is_empty()
    assert not d.equivalent_to(c) and d.equivalence_counterexample(c) is not None
    assert c.complement().equivalent_to(d)
    assert d.normalized().equivalent_to(d) and d.streamlined().equivalent_to(d)
    low = {col for q in d.normalized().states() for (_, _, col, _) in d.normalized().edges_from(q)}
    assert len(low) == 3
    assert d.streamlined().num_states <= d.num_states


def test_dpa_complement_of_degenerate_automata():
    empty = DPA(AB, 1, 0, [])
    assert empty.complement().num_edges == 0
    full_range = DPA(AB, 2, 0, [(0, "a", 0, 1), (0, "b", 255, 1), (1, "a", 1, 0), (1, "b", 2, 0)])
    assert full_range.complement().equivalent_to(full_range.complement().complement().complement())


def test_dpa_comparisons():
    d = DPA(AB, 1, 0, INF_B)
    never = DPA(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 1, 0)])
    assert never.included_in(d) and not d.included_in(never)
    assert d.equivalent_to(DPA(AB, 1, 0, INF_B)) and d.equivalence_counterexample(DPA(AB, 1, 0, INF_B)) is None
    cex = d.inclusion_counterexample(never)
    assert d.accepts(cex) and not never.accepts(cex)


def test_prop_dpa():
    d = PropDPA(P, 1, 0, [(0, T, 0, 0), (0, F, 1, 0)])
    assert d.accepts(w([F], [T, F])) and not d.accepts(w([T], [F]))
    assert d.complement().accepts(w([T], [F]))
    assert d.rejected_word() is not None
    assert d.equivalent_to(d.streamlined())


def test_color_range():
    for cls, args in [(DPA, ()), (DRA, ([],)), (DMA, ([],))]:
        with pytest.raises(OverflowError):
            cls(AB, 1, 0, [(0, "a", 256, 0)], *args)
        with pytest.raises(OverflowError):
            cls(AB, 1, 0, [(0, "a", -1, 0)], *args)


def test_invalid_construction():
    for cls, args in [(DCA, ()), (DPA, ()), (DRA, ([],)), (DMA, ([],))]:
        c = True if cls is DCA else 0
        with pytest.raises(ValueError):
            cls(AB, 1, 1, [], *args)
        with pytest.raises(ValueError):
            cls(AB, 1, 0, [(0, "a", c, 1)], *args)
        with pytest.raises(ValueError):
            cls(AB, 1, 0, [(0, "z", c, 0)], *args)
        with pytest.raises(ValueError):
            cls(AB, 0, 0, [], *args)


def test_dra():
    d = DRA(AB, 2, 0, TWO_STATE, [([], [1])])
    assert d.accepts(w("", "ba")) and not d.accepts(w("b", "a"))
    assert not d.is_empty() and d.accepts(d.accepting_word())
    # fin and inf: color 1 forbidden, color 0 required: only finitely many b
    fin_b = DRA(AB, 2, 0, TWO_STATE, [([1], [0])])
    assert fin_b.accepts(w("bb", "a")) and not fin_b.accepts(w("", "ab"))
    # several pairs: one satisfied pair is enough
    both = DRA(AB, 2, 0, TWO_STATE, [([1], [0]), ([], [1])])
    assert both.accepts(w("bb", "a")) and both.accepts(w("", "ab")) and both.accepts(w("", "b"))
    assert DRA(AB, 2, 0, TWO_STATE, []).is_empty()
    assert DRA(AB, 2, 0, TWO_STATE, [([0, 1], [0])]).accepting_word() is None
    assert d.edges_from(0) and d.sccs()
    assert not hasattr(d, "included_in")


def test_prop_dra():
    d = PropDRA(P, 1, 0, [(0, T, 1, 0), (0, F, 0, 0)], [([], [1])])
    assert d.accepts(w([F], [T])) and not d.accepts(w([T], [F]))
    assert d.accepting_word() is not None


def test_dma():
    d = DMA(AB, 2, 0, TWO_STATE, [[0], [1]])
    assert d.accepts(w("", "a")) and d.accepts(w("", "b")) and not d.accepts(w("", "ba"))
    both = DMA(AB, 2, 0, TWO_STATE, [[0, 1]])
    assert both.accepts(w("", "ba")) and not both.accepts(w("", "a"))
    assert both.accepts(both.accepting_word())
    assert DMA(AB, 2, 0, TWO_STATE, []).is_empty()
    assert DMA(AB, 2, 0, TWO_STATE, [[7]]).accepting_word() is None
    assert DMA(AB, 2, 0, TWO_STATE, [[1, 0]]).accepts(w("", "ba"))  # order does not matter


def test_prop_dma():
    d = PropDMA(P, 1, 0, [(0, T, 1, 0), (0, F, 0, 0)], [[0], [1]])
    assert d.accepts(w([], [T])) and not d.accepts(w([], [T, F]))


def test_builders():
    b = DCABuilder(AB)
    q = b.add_state()
    assert q == 0 and b.add_state() == 1 and b.num_states == 2
    b.add_edge(0, "a", True, 1)
    b.add_edge(0, "b", False, 0)
    b.add_edge(1, "a", False, 1)
    b.add_edge(1, "b", False, 1)
    with pytest.raises(ValueError):
        b.build()
    b.set_initial(0)
    d = b.build()
    assert isinstance(d, DCA) and d.num_states == 2 and d.accepts(w("a", "b"))
    assert d.accepts(w("", "b")) and d.edges_from(0) == b.build().edges_from(0)
    b.add_edge(0, "a", False, 0)  # the builder can be used further and replaces edges
    assert b.build().num_edges == d.num_edges


def test_builder_validation():
    b = DPABuilder(AB)
    b.add_state()
    with pytest.raises(ValueError):
        b.add_edge(0, "a", 0, 1)
    with pytest.raises(ValueError):
        b.add_edge(1, "a", 0, 0)
    with pytest.raises(ValueError):
        b.add_edge(0, "c", 0, 0)
    with pytest.raises(ValueError):
        b.add_edge(0, "ab", 0, 0)
    with pytest.raises(ValueError):
        b.add_edge(0, "a", 256, 0)
    with pytest.raises(ValueError):
        b.add_edge(0, "a", -1, 0)
    with pytest.raises(TypeError):
        b.add_edge(0, "a", "x", 0)
    with pytest.raises(TypeError):
        b.add_edge(0, 1, 0, 0)
    with pytest.raises(TypeError):
        b.add_edge("0", "a", 0, 0)
    with pytest.raises(ValueError):
        b.set_initial(1)
    with pytest.raises(ValueError):
        b.set_initial(-1)
    with pytest.raises(TypeError):
        DCABuilder(P)
    with pytest.raises(TypeError):
        PropDCABuilder(AB)
    c = DCABuilder(AB)
    c.add_state()
    with pytest.raises(TypeError):
        c.add_edge(0, "a", 1, 0)
    with pytest.raises(ValueError):
        DRABuilder(AB, [([300], [])])
    with pytest.raises(ValueError):
        DMABuilder(AB, [[-1]])


def test_all_builders_build():
    inf_b = [(0, "a", 1, 0), (0, "b", 0, 0)]

    def run(builder, edges):
        q = builder.add_state()
        for s, c in edges:
            builder.add_edge(q, s, c, q)
        builder.set_initial(q)
        return builder.build()

    d = run(DPABuilder(AB), [("a", 1), ("b", 0)])
    assert isinstance(d, DPA) and d.equivalent_to(DPA(AB, 1, 0, inf_b))
    d = run(PropDPABuilder(P), [(T, 1), (F, 0)])
    assert isinstance(d, PropDPA) and d.accepts(w([T], [F]))
    d = run(PropDCABuilder(P), [(T, True), (F, False)])
    assert isinstance(d, PropDCA) and d.accepts(w([T], [F]))
    d = run(DRABuilder(AB, [([], [1])]), [("a", 0), ("b", 1)])
    assert isinstance(d, DRA) and d.accepts(w("", "ab"))
    d = run(PropDRABuilder(P, [([], [1])]), [(T, 1), (F, 0)])
    assert isinstance(d, PropDRA) and d.accepts(w([T], [F, T]))
    d = run(DMABuilder(AB, [[0, 1]]), [("a", 0), ("b", 1)])
    assert isinstance(d, DMA) and d.accepts(w("", "ab")) and not d.accepts(w("", "a"))
    d = run(PropDMABuilder(P, [[0, 1]]), [(T, 1), (F, 0)])
    assert isinstance(d, PropDMA) and d.accepts(w([], [T, F]))


def test_exports():
    for name in ["DCA", "PropDPA", "DRA", "PropDMA", "DBABuilder", "PropDMABuilder", "DRABuilder"]:
        assert name in automata.__all__ and hasattr(automata, name)
