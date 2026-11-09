"""The complement of the deterministic omega classes that is just a change of the condition,
checked against `accepts` on many ultimately periodic words."""

import itertools
import random

import pytest

from automata import (
    DBA,
    DCA,
    DMA,
    DRA,
    DSA,
    CharAlphabet,
    OmegaWord,
    PropDBA,
    PropDCA,
    PropDRA,
    PropDSA,
)

AB = CharAlphabet("ab")


def lassos(letters="ab", prefix=3, period=3):
    words = lambda n: ["".join(w) for w in itertools.product(letters, repeat=n)]
    return [
        OmegaWord(u, v)
        for lu in range(prefix + 1)
        for u in words(lu)
        for lv in range(1, period + 1)
        for v in words(lv)
    ]


LASSOS = lassos()


def random_edges(rng, num_states, color):
    return [
        (q, a, color(rng), rng.randrange(num_states))
        for q in range(num_states)
        for a in "ab"
    ]


def assert_complements(aut, other):
    for w in LASSOS:
        assert aut.accepts(w) != other.accepts(w), (w.prefix, w.period)


@pytest.mark.parametrize("seed", range(20))
def test_buchi_and_co_buchi(seed):
    rng = random.Random(seed)
    n = rng.randrange(1, 5)
    edges = random_edges(rng, n, lambda r: r.random() < 0.3)
    dba = DBA(AB, n, 0, edges)
    dca = dba.complement()
    assert isinstance(dca, DCA)
    assert dca.edges_from(0) == dba.edges_from(0)
    assert_complements(dba, dca)
    back = dca.complement()
    assert isinstance(back, DBA)
    assert back.equivalent_to(dba)


def test_prop_buchi_and_co_buchi():
    dba = PropDBA.from_hoa(DBA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)]).to_hoa())
    assert isinstance(dba.complement(), PropDCA)
    assert isinstance(dba.complement().complement(), PropDBA)
    assert dba.complement().complement().equivalent_to(dba)
    assert not dba.complement().is_empty()


@pytest.mark.parametrize("seed", range(20))
def test_rabin_and_streett(seed):
    rng = random.Random(seed)
    n = rng.randrange(1, 5)
    edges = random_edges(rng, n, lambda r: r.randrange(4))
    pairs = [
        (
            rng.sample(range(4), rng.randrange(3)),
            rng.sample(range(4), rng.randrange(3)),
        )
        for _ in range(rng.randrange(0, 4))
    ]
    dra = DRA(AB, n, 0, edges, pairs)
    dsa = dra.complement()
    assert isinstance(dsa, DSA)
    assert_complements(dra, dsa)
    back = dsa.complement()
    assert isinstance(back, DRA)
    for w in LASSOS:
        assert back.accepts(w) == dra.accepts(w)
    # the Streett automaton with the pairs given directly is the same as the complement
    direct = DSA(AB, n, 0, edges, [(inf, fin) for fin, inf in pairs])
    for w in LASSOS:
        assert direct.accepts(w) == dsa.accepts(w)


def test_rabin_without_pairs_and_prop():
    empty = DRA(AB, 1, 0, [(0, "a", 0, 0), (0, "b", 0, 0)], [])
    assert not empty.accepts(OmegaWord("", "a"))
    assert empty.complement().accepts(OmegaWord("", "a"))
    prop = PropDRA.from_hoa(
        DRA(AB, 1, 0, [(0, "a", 0, 0), (0, "b", 1, 0)], [([0], [1])]).to_hoa()
    )
    assert isinstance(prop.complement(), PropDSA)
    assert isinstance(prop.complement().complement(), PropDRA)


@pytest.mark.parametrize("seed", range(20))
def test_muller(seed):
    rng = random.Random(seed)
    n = rng.randrange(1, 5)
    edges = random_edges(rng, n, lambda r: r.randrange(3))
    sets = [rng.sample(range(3), rng.randrange(1, 4)) for _ in range(rng.randrange(0, 5))]
    dma = DMA(AB, n, 0, edges, sets)
    comp = dma.complement()
    assert isinstance(comp, DMA)
    assert_complements(dma, comp)
    twice = comp.complement()
    for w in LASSOS:
        assert twice.accepts(w) == dma.accepts(w)


def test_muller_with_too_many_colors():
    edges = [(q, "a", q, (q + 1) % 17) for q in range(17)]
    dma = DMA(CharAlphabet("a"), 17, 0, edges, [[0]])
    with pytest.raises(ValueError):
        dma.complement()
    sixteen = DMA(CharAlphabet("a"), 16, 0, edges[:15] + [(15, "a", 15, 0)], [[0]])
    assert sixteen.complement().accepts(OmegaWord("", "a"))


def test_muller_with_a_set_of_unused_colors():
    dma = DMA(CharAlphabet("a"), 1, 0, [(0, "a", 0, 0)], [[7], [0]])
    assert dma.accepts(OmegaWord("", "a"))
    assert not dma.complement().accepts(OmegaWord("", "a"))


@pytest.mark.parametrize("seed", range(20))
def test_dba_streamlined(seed):
    rng = random.Random(seed)
    n = rng.randrange(1, 6)
    dba = DBA(AB, n, 0, random_edges(rng, n, lambda r: r.random() < 0.4))
    streamlined = dba.streamlined()
    assert isinstance(streamlined, DBA)
    assert streamlined.num_states <= dba.num_states
    assert streamlined.equivalent_to(dba)
    for w in LASSOS:
        assert streamlined.accepts(w) == dba.accepts(w)
