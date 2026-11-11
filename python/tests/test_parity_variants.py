"""The four parity classes (min even, max even, min odd, max odd), their conversions and HOA."""

import random
from itertools import product

import pytest

import automata
from automata import (
    DPA,
    DPAMaxEven,
    DPAMaxOdd,
    DPAMinOdd,
    CharAlphabet,
    HoaError,
    OmegaWord,
    PropAlphabet,
    PropDPA,
    PropDPAMaxEven,
    PropDPAMaxOdd,
    PropDPAMinOdd,
    PropDBA,
    PropDCA,
    parse_hoa,
    parse_hoa_all,
)

AB = CharAlphabet("ab")
P = PropAlphabet(["p"])
T, F = [True], [False]

# class, Prop class, `min`/`max`, accepted parity of the deciding color
KINDS = [
    (DPA, PropDPA, min, 0),
    (DPAMaxEven, PropDPAMaxEven, max, 0),
    (DPAMinOdd, PropDPAMinOdd, min, 1),
    (DPAMaxOdd, PropDPAMaxOdd, max, 1),
]
# the class of the complement (`DPA.complement` is the normalizing complement of the crate, it stays a DPA)
DUAL = {DPA: DPA, DPAMinOdd: DPA, DPAMaxEven: DPAMaxOdd, DPAMaxOdd: DPAMaxEven}
VARIANTS = KINDS[1:]

LASSOS = [
    ("".join(prefix), "".join(period))
    for lp in range(3)
    for prefix in product("ab", repeat=lp)
    for lv in range(1, 4)
    for period in product("ab", repeat=lv)
]


def random_edges(rng, num_states, num_colors):
    """A complete automaton over `AB`."""
    return [(q, s, rng.randrange(num_colors), rng.randrange(num_states)) for q in range(num_states) for s in "ab"]


def reference(edges, pick, parity, prefix, period):
    """Decides acceptance without the library: the colors seen infinitely often are the ones of the final cycle."""
    delta = {(q, s): (c, t) for q, s, c, t in edges}
    q = 0
    for s in prefix:
        q = delta[q, s][1]
    starts, passes = [], []
    while q not in starts:
        starts.append(q)
        colors = set()
        for s in period:
            c, q = delta[q, s]
            colors.add(c)
        passes.append(colors)
    inf = set().union(*passes[starts.index(q) :])
    return pick(inf) % 2 == parity


def verdicts(aut, lassos=LASSOS):
    return [aut.accepts(OmegaWord(prefix, period)) for prefix, period in lassos]


def automata_of(rng, count=25):
    for _ in range(count):
        n = rng.randrange(1, 5)
        yield random_edges(rng, n, rng.randrange(1, 7)), n


@pytest.mark.parametrize("cls, _prop, pick, parity", KINDS)
def test_accepts_agrees_with_the_definition(cls, _prop, pick, parity):
    for edges, n in automata_of(random.Random(1)):
        aut = cls(AB, n, 0, edges)
        expected = [reference(edges, pick, parity, *lasso) for lasso in LASSOS]
        assert verdicts(aut) == expected


@pytest.mark.parametrize("cls, _prop, _pick, _parity", VARIANTS)
def test_to_min_even_is_equivalent(cls, _prop, _pick, _parity):
    rng = random.Random(2)
    for edges, n in automata_of(rng, 40):
        aut = cls(AB, n, 0, edges)
        converted = aut.to_min_even()
        assert type(converted) is DPA
        assert (converted.num_states, converted.num_edges, converted.initial) == (n, 2 * n, 0)
        assert verdicts(converted) == verdicts(aut)


@pytest.mark.parametrize("cls, _prop, _pick, _parity", KINDS)
def test_complement_accepts_exactly_the_rejected_words(cls, _prop, _pick, _parity):
    for edges, n in automata_of(random.Random(3)):
        aut = cls(AB, n, 0, edges)
        comp = aut.complement()
        assert type(comp) is DUAL[cls]
        assert verdicts(comp) == [not v for v in verdicts(aut)]
        assert verdicts(comp.complement()) == verdicts(aut)
        if cls is not DPA:
            # same transitions and colors, only the condition is dual
            assert (comp.num_states, comp.num_edges) == (aut.num_states, aut.num_edges)
            assert sorted(comp.edges_from(0)) == sorted(aut.edges_from(0))


def test_dpa_keeps_its_methods():
    d = DPA(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 0, 0)])
    assert type(d.complement()) is DPA and d.complement().accepts(OmegaWord("b", "a"))
    assert type(d.normalized()) is DPA and d.equivalent_to(d.streamlined())
    assert d.rejected_word() is not None
    assert not hasattr(DPAMaxEven, "equivalent_to") and not hasattr(DPAMaxEven, "normalized")


@pytest.mark.parametrize("cls, _prop, pick, parity", KINDS)
def test_emptiness_and_accepting_word(cls, _prop, pick, parity):
    rng = random.Random(4)
    for edges, n in automata_of(rng, 40):
        aut = cls(AB, n, 0, edges)
        word = aut.accepting_word()
        accepted = [lasso for lasso in LASSOS if reference(edges, pick, parity, *lasso)]
        if word is None:
            assert aut.is_empty() and not accepted
        else:
            assert not aut.is_empty() and aut.accepts(word)


def test_is_empty_on_trivial_automata():
    loop = lambda c: [(0, "a", c, 0), (0, "b", c, 0)]  # noqa: E731
    assert DPAMaxEven(AB, 1, 0, loop(1)).is_empty() and DPAMaxEven(AB, 1, 0, loop(2)).accepting_word() is not None
    assert DPAMinOdd(AB, 1, 0, loop(0)).is_empty() and not DPAMinOdd(AB, 1, 0, loop(3)).is_empty()
    assert DPAMaxOdd(AB, 1, 0, loop(2)).is_empty() and not DPAMaxOdd(AB, 1, 0, loop(1)).is_empty()


def test_to_min_even_overflow_is_a_value_error():
    # a max kind needs the color `c - p` with the least `c >= 255` of the right parity: 256 for even
    edges = [(0, "a", 0, 0), (0, "b", 255, 0)]
    aut = DPAMaxEven(AB, 1, 0, edges)
    for method in (aut.to_min_even, aut.is_empty, aut.accepting_word):
        with pytest.raises(ValueError, match="255"):
            method()
    # the smallest color counts: 256 - 1 fits
    assert DPAMaxEven(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 255, 0)]).to_min_even() is not None
    assert DPAMaxOdd(AB, 1, 0, edges).to_min_even() is not None  # c = 255
    with pytest.raises(ValueError):
        DPAMinOdd(AB, 1, 0, [(0, "a", 255, 0), (0, "b", 0, 0)]).to_min_even()
    assert DPAMinOdd(AB, 1, 0, [(0, "a", 254, 0), (0, "b", 0, 0)]).to_min_even() is not None


@pytest.mark.parametrize("cls", [DPAMaxEven, DPAMinOdd, DPAMaxOdd])
def test_constructor_validates_its_arguments(cls):
    ok = [(0, "a", 0, 0), (0, "b", 1, 0)]
    assert cls(AB, 1, 0, ok).num_edges == 2
    for bad_edges in ([(0, "c", 0, 0)], [(1, "a", 0, 0)], [(0, "a", 0, 1)], [(0, "ab", 0, 0)]):
        with pytest.raises(ValueError):
            cls(AB, 1, 0, bad_edges)
    with pytest.raises(OverflowError):
        cls(AB, 1, 0, [(0, "a", 256, 0)])
    with pytest.raises(ValueError):
        cls(AB, 1, 1, ok)
    with pytest.raises(IndexError):
        cls(AB, 1, 0, ok).edges_from(1)
    assert sorted(cls(AB, 2, 0, ok).sccs()) == [[0], [1]]
    assert cls(AB, 1, 0, ok).states() == [0] and cls(AB, 1, 0, ok).alphabet == AB
    assert cls.__name__ in repr(cls(AB, 1, 0, ok))


def test_a_later_edge_replaces_an_earlier_one():
    d = DPAMaxOdd(AB, 1, 0, [(0, "a", 0, 0), (0, "a", 1, 0), (0, "b", 0, 0)])
    assert d.num_edges == 2 and d.accepts(OmegaWord("", "a"))


def test_prop_classes_use_propositions():
    for _cls, prop, _pick, _parity in KINDS:
        d = prop(P, 1, 0, [(0, T, 1, 0), (0, F, 2, 0)])
        assert isinstance(d.accepts(OmegaWord([], [T])), bool)
        with pytest.raises(TypeError):
            d.accepts(OmegaWord("a", "b"))
        with pytest.raises(ValueError):
            prop(P, 1, 0, [(0, [True, True], 1, 0)])


def random_prop_edges(rng, num_states, num_colors):
    return [(q, s, rng.randrange(num_colors), rng.randrange(num_states)) for q in range(num_states) for s in (T, F)]


PROP_LASSOS = [
    (list(prefix), list(period))
    for lp in range(3)
    for prefix in product((T, F), repeat=lp)
    for lv in range(1, 4)
    for period in product((T, F), repeat=lv)
]


def prop_verdicts(aut):
    return [aut.accepts(OmegaWord(prefix, period)) for prefix, period in PROP_LASSOS]


@pytest.mark.parametrize("_cls, prop, _pick, _parity", KINDS)
def test_hoa_round_trip_keeps_class_and_language(_cls, prop, _pick, _parity):
    rng = random.Random(5)
    for _ in range(20):
        n = rng.randrange(1, 4)
        aut = prop(P, n, 0, random_prop_edges(rng, n, rng.randrange(1, 6)))
        text = aut.to_hoa()
        back = prop.from_hoa(text)
        assert type(back) is prop and (back.num_states, back.initial) == (n, 0)
        assert prop_verdicts(back) == prop_verdicts(aut)
        parsed = parse_hoa(text)
        assert type(parsed) is prop and prop_verdicts(parsed) == prop_verdicts(aut)
        assert [type(a) for a in parse_hoa_all(text + text)] == [prop, prop]


def test_the_hoa_header_names_the_kind():
    for cls, name in ((DPA, "min even"), (DPAMaxEven, "max even"), (DPAMinOdd, "min odd"), (DPAMaxOdd, "max odd")):
        assert f"acc-name: parity {name}" in cls(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 0, 0)]).to_hoa()


@pytest.mark.parametrize("_cls, prop, _pick, _parity", KINDS)
def test_from_hoa_reads_exactly_its_own_kind(_cls, prop, _pick, _parity):
    aut_of = {p: p(P, 1, 0, [(0, T, 1, 0), (0, F, 0, 0)]) for _, p, _, _ in KINDS}
    for other, aut in aut_of.items():
        if other is prop or prop is PropDPA:
            assert type(prop.from_hoa(aut.to_hoa())) is prop
        else:
            with pytest.raises(HoaError, match="parity"):
                prop.from_hoa(aut.to_hoa())
    if prop is not PropDPA:
        for text in (
            PropDBA(P, 1, 0, [(0, T, True, 0), (0, F, False, 0)]).to_hoa(),
            PropDCA(P, 1, 0, [(0, T, True, 0), (0, F, False, 0)]).to_hoa(),
        ):
            with pytest.raises(HoaError):
                prop.from_hoa(text)


def test_prop_dpa_normalizes_every_kind_to_min_even():
    rng = random.Random(6)
    for _, prop, _, _ in KINDS:
        for _ in range(15):
            n = rng.randrange(1, 4)
            aut = prop(P, n, 0, random_prop_edges(rng, n, rng.randrange(1, 6)))
            normalized = PropDPA.from_hoa(aut.to_hoa())
            assert type(normalized) is PropDPA
            assert prop_verdicts(normalized) == prop_verdicts(aut)
            if prop is not PropDPA:
                assert prop_verdicts(normalized) == prop_verdicts(aut.to_min_even())


def test_prop_dpa_reads_buchi_and_co_buchi():
    dba = PropDBA(P, 1, 0, [(0, T, True, 0), (0, F, False, 0)])
    dca = PropDCA(P, 1, 0, [(0, T, True, 0), (0, F, False, 0)])
    for aut in (dba, dca):
        dpa = PropDPA.from_hoa(aut.to_hoa())
        assert type(dpa) is PropDPA and prop_verdicts(dpa) == prop_verdicts(aut)


def test_prop_dpa_reports_priorities_that_do_not_fit():
    aut = PropDPAMaxEven(P, 1, 0, [(0, T, 0, 0), (0, F, 255, 0)])
    text = aut.to_hoa()
    assert prop_verdicts(PropDPAMaxEven.from_hoa(text)) == prop_verdicts(aut)
    with pytest.raises(automata.AcceptanceError):
        PropDPA.from_hoa(text)
    with pytest.raises(ValueError):
        aut.to_min_even()


def test_variants_validate_the_priorities_of_the_file():
    text = PropDPAMaxOdd(P, 1, 0, [(0, T, 1, 0), (0, F, 2, 0)]).to_hoa()
    for bad in (text.replace("{2}", "{9}"),):
        with pytest.raises((HoaError, automata.AcceptanceError)):
            PropDPAMaxOdd.from_hoa(bad)


def test_parse_hoa_all_returns_the_class_of_every_automaton():
    texts = [prop(P, 1, 0, [(0, T, 1, 0), (0, F, 0, 0)]).to_hoa() for _, prop, _, _ in KINDS]
    assert [type(a) for a in parse_hoa_all("\n".join(texts))] == [prop for _, prop, _, _ in KINDS]
