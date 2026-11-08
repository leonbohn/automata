"""Streett automata (DSA) and the HOA input/output of Rabin and Streett automata."""

import random
from itertools import product

import pytest

import automata
from automata import (
    DRA,
    DSA,
    CharAlphabet,
    HoaError,
    OmegaWord,
    PropAlphabet,
    PropDRA,
    PropDSA,
    parse_hoa,
    parse_hoa_all,
)

AB = CharAlphabet("ab")
P = PropAlphabet(["p"])
T, F = [True], [False]

LASSOS = [
    ("".join(prefix), "".join(period))
    for lp in range(3)
    for prefix in product("ab", repeat=lp)
    for lv in range(1, 4)
    for period in product("ab", repeat=lv)
]
PROP_LASSOS = [
    (list(prefix), list(period))
    for lp in range(3)
    for prefix in product((T, F), repeat=lp)
    for lv in range(1, 4)
    for period in product((T, F), repeat=lv)
]


def rabin_holds(pairs, inf):
    return any(not set(fin) & inf and set(i) & inf for fin, i in pairs)


def streett_holds(pairs, inf):
    return all(not set(fin) & inf or set(i) & inf for fin, i in pairs)


def infinitely_often(delta, initial, prefix, period):
    """The labels of the edges that the run takes infinitely often (delta maps (state, symbol) to (label, target))."""
    q = initial
    for s in prefix:
        q = delta[q, s][1]
    starts, passes = [], []
    while q not in starts:
        starts.append(q)
        labels = []
        for s in period:
            label, q = delta[q, s]
            labels.append(label)
        passes.append(labels)
    return [label for labels in passes[starts.index(q) :] for label in labels]


def random_case(rng):
    n = rng.randrange(1, 5)
    num_colors = rng.randrange(1, 5)
    edges = [(q, s, rng.randrange(num_colors), rng.randrange(n)) for q in range(n) for s in "ab"]
    sets = lambda: rng.sample(range(num_colors), rng.randrange(num_colors + 1))  # noqa: E731
    pairs = [(sets(), sets()) for _ in range(rng.randrange(0, 4))]
    return n, edges, pairs


def reference(holds, edges, pairs, lasso):
    delta = {(q, s): (c, t) for q, s, c, t in edges}
    return holds(pairs, set(infinitely_often(delta, 0, *lasso)))


def verdicts(aut, lassos=LASSOS):
    return [aut.accepts(OmegaWord(prefix, period)) for prefix, period in lassos]


def test_dsa_and_dra_agree_with_the_definition():
    rng = random.Random(1)
    for _ in range(60):
        n, edges, pairs = random_case(rng)
        assert verdicts(DRA(AB, n, 0, edges, pairs)) == [reference(rabin_holds, edges, pairs, w) for w in LASSOS]
        assert verdicts(DSA(AB, n, 0, edges, pairs)) == [reference(streett_holds, edges, pairs, w) for w in LASSOS]


def test_the_streett_automaton_with_swapped_pairs_accepts_the_complement_of_the_rabin_automaton():
    rng = random.Random(2)
    for _ in range(60):
        n, edges, pairs = random_case(rng)
        rabin = DRA(AB, n, 0, edges, pairs)
        streett = DSA(AB, n, 0, edges, [(inf, fin) for fin, inf in pairs])
        assert verdicts(streett) == [not v for v in verdicts(rabin)]
        if rabin.is_empty():
            assert all(verdicts(streett))


def test_emptiness_and_accepting_word():
    rng = random.Random(3)
    for _ in range(80):
        n, edges, pairs = random_case(rng)
        for cls, holds in ((DRA, rabin_holds), (DSA, streett_holds)):
            aut = cls(AB, n, 0, edges, pairs)
            word = aut.accepting_word()
            if word is None:
                assert aut.is_empty()
                assert not any(reference(holds, edges, pairs, w) for w in LASSOS)
            else:
                assert not aut.is_empty() and aut.accepts(word)


def test_without_pairs_dra_rejects_everything_and_dsa_accepts_everything():
    loop = [(0, "a", 0, 0), (0, "b", 1, 0)]
    dra, dsa = DRA(AB, 1, 0, loop, []), DSA(AB, 1, 0, loop, [])
    assert dra.is_empty() and dra.accepting_word() is None and not any(verdicts(dra))
    assert not dsa.is_empty() and all(verdicts(dsa))


def test_dsa_example_of_the_documentation():
    edges = [(0, "a", 0, 0), (0, "b", 1, 0)]
    # b has to be seen infinitely often or a only finitely often
    d = DSA(AB, 1, 0, edges, [([0], [1])])
    assert d.accepts(OmegaWord("a", "b")) and d.accepts(OmegaWord("", "ab")) and not d.accepts(OmegaWord("", "a"))
    assert d.sccs() == [[0]] and d.states() == [0] and (d.num_states, d.num_edges, d.initial) == (1, 2, 0)
    assert d.edges_from(0) and "DSA" in repr(d)
    assert not hasattr(d, "complement")  # take the DRA with swapped pairs


@pytest.mark.parametrize("cls", [DRA, DSA])
def test_constructor_validates_its_arguments(cls):
    ok = [(0, "a", 0, 0), (0, "b", 1, 0)]
    for bad_edges in ([(0, "c", 0, 0)], [(1, "a", 0, 0)], [(0, "a", 0, 1)], [(0, "ab", 0, 0)]):
        with pytest.raises(ValueError):
            cls(AB, 1, 0, bad_edges, [])
    with pytest.raises(ValueError):
        cls(AB, 1, 1, ok, [])
    with pytest.raises(OverflowError):
        cls(AB, 1, 0, [(0, "a", 256, 0)], [])
    with pytest.raises(OverflowError):
        cls(AB, 1, 0, ok, [([256], [])])
    with pytest.raises(TypeError):
        cls(AB, 1, 0, ok)
    with pytest.raises(IndexError):
        cls(AB, 1, 0, ok, []).edges_from(1)
    with pytest.raises(TypeError):
        cls(AB, 1, 0, ok, []).accepts(OmegaWord([T], [F]))


def test_prop_classes():
    edges = [(0, T, 0, 0), (0, F, 1, 0)]
    for cls in (PropDRA, PropDSA):
        aut = cls(P, 1, 0, edges, [([0], [1])])
        assert verdicts(aut, PROP_LASSOS) == verdicts(cls(P, 1, 0, edges, [([0], [1])]), PROP_LASSOS)
        with pytest.raises(ValueError):
            cls(P, 1, 0, [(0, [True, True], 0, 0)], [])
        with pytest.raises(TypeError):
            aut.accepts(OmegaWord("a", "b"))


def standard_pairs(k):
    return [([2 * i], [2 * i + 1]) for i in range(k)]


@pytest.mark.parametrize("char, prop", [(DRA, PropDRA), (DSA, PropDSA)])
def test_hoa_round_trip(char, prop):
    rng = random.Random(4)
    for _ in range(30):
        # the Streett condition of several pairs is written without the parentheses it needs, see below
        n, k = rng.randrange(1, 4), rng.randrange(1, 3) if prop is PropDRA else 1
        edges = [(q, s, rng.randrange(2 * k), rng.randrange(n)) for q in range(n) for s in (T, F)]
        aut = prop(P, n, 0, edges, standard_pairs(k))
        text = aut.to_hoa()
        assert f"acc-name: {'Rabin' if prop is PropDRA else 'Streett'} {k}" in text
        back = prop.from_hoa(text)
        assert type(back) is prop and (back.num_states, back.num_edges, back.initial) == (n, 2 * n, 0)
        assert verdicts(back, PROP_LASSOS) == verdicts(aut, PROP_LASSOS)
        assert type(parse_hoa(text)) is prop
        # the other condition is not read
        other = PropDSA if prop is PropDRA else PropDRA
        with pytest.raises(HoaError, match="required"):
            other.from_hoa(text)
    # character automata are written as propositions
    char_aut = char(AB, 1, 0, [(0, "a", 0, 0), (0, "b", 1, 0)], standard_pairs(1))
    assert type(parse_hoa(char_aut.to_hoa())) is prop
    assert [type(a) for a in parse_hoa_all(char_aut.to_hoa() * 2)] == [prop, prop]


@pytest.mark.xfail(strict=True, reason="the crate writes `(Fin(0)) | (Inf(1)) & (Fin(2)) | (Inf(3))` for two pairs")
def test_hoa_round_trip_of_two_streett_pairs():
    aut = PropDSA(P, 1, 0, [(0, T, 0, 0), (0, F, 3, 0)], standard_pairs(2))
    assert verdicts(PropDSA.from_hoa(aut.to_hoa()), PROP_LASSOS) == verdicts(aut, PROP_LASSOS)


def hoa_text(name, formula, num_sets, states):
    """`states[q]` are the edges `(symbol, target, mask)` of the state `q`, the symbols are 0 (`p`) and 1 (`!p`)."""
    lines = ["HOA: v1", f"States: {len(states)}", "Start: 0", f"acc-name: {name}", f"Acceptance: {num_sets} {formula}"]
    lines += ['AP: 1 "p"', "--BODY--"]
    for q, edges in enumerate(states):
        lines.append(f"State: {q}")
        for symbol, target, mask in edges:
            guard = "0" if symbol == 0 else "!0"
            lines.append(f"[{guard}] {target} {{{' '.join(map(str, sorted(mask)))}}}")
    lines.append("--END--")
    return "\n".join(lines)


def formula(pairs, rabin):
    def term(sets, name, join, none):
        return join.join(f"{name}({i})" for i in sets) if sets else none

    parts = [
        f"({term(fin, 'Fin', ' & ', 't')}) {'&' if rabin else '|'} ({term(inf, 'Inf', ' | ', 'f')})" for fin, inf in pairs
    ]
    return (" | " if rabin else " & ").join(f"({p})" for p in parts)


@pytest.mark.parametrize("rabin", [True, False])
def test_from_hoa_numbers_the_sets_of_acceptance_sets_as_colors(rabin):
    prop, holds = (PropDRA, rabin_holds) if rabin else (PropDSA, streett_holds)
    rng = random.Random(5)
    for _ in range(80):
        num_sets = rng.randrange(1, 6)
        some = lambda: rng.sample(range(num_sets), rng.randrange(num_sets + 1))  # noqa: E731
        pairs = [(some(), some()) for _ in range(rng.randrange(1, 4))]
        # a pair that is `Fin(0) & Inf(1)` and `Fin(0)` has to be spelled with sets, so every pair needs a set
        n = rng.randrange(1, 5)
        states = [[(s, rng.randrange(n), some()) for s in (0, 1)] for _ in range(n)]
        aut = prop.from_hoa(hoa_text(f"{'Rabin' if rabin else 'Streett'} {len(pairs)}", formula(pairs, rabin), num_sets, states))
        # the masks are numbered in the order of their first occurrence
        colors = [c for q in aut.states() for (_, _, c, _) in aut.edges_from(q)]
        first = list(dict.fromkeys(colors))
        assert first == list(range(len(first)))
        masks = {frozenset(m) for edges in states for (_, _, m) in edges}
        assert len(first) == len(masks)
        delta = {(q, s): (frozenset(m), t) for q, edges in enumerate(states) for (s, t, m) in edges}
        for prefix, period in PROP_LASSOS:
            sym = lambda x: 0 if x == T else 1  # noqa: E731
            inf = infinitely_often(delta, 0, [sym(x) for x in prefix], [sym(x) for x in period])
            seen = set().union(*inf)
            assert aut.accepts(OmegaWord(prefix, period)) == holds(pairs, seen), (pairs, states)


def test_the_empty_set_of_acceptance_sets_is_a_color():
    text = hoa_text("Rabin 1", "(Fin(0)) & (Inf(1))", 2, [[(0, 0, [1]), (1, 0, [])]])
    aut = PropDRA.from_hoa(text)
    assert sorted(c for (_, _, c, _) in aut.edges_from(0)) == [0, 1]
    assert aut.accepts(OmegaWord([], [T, F])) and not aut.accepts(OmegaWord([], [F]))


def test_from_hoa_accepts_256_but_not_257_different_masks():
    def text(k):
        states = [[(0, (q + 1) % k, [i for i in range(9) if q >> i & 1]), (1, 0, [0])] for q in range(k)]
        return hoa_text("Rabin 1", "(Fin(0)) & (Inf(1))", 9, states)

    # 256 masks come from the states, `{0}` of the second edges is among them
    assert PropDRA.from_hoa(text(256)).num_states == 256
    with pytest.raises(HoaError, match="more than 256"):
        PropDRA.from_hoa(text(300))
    with pytest.raises(HoaError, match="more than 256"):
        parse_hoa(text(300))


def test_nondeterministic_rabin_and_streett_are_not_implemented():
    for rabin in (True, False):
        text = hoa_text(
            "Rabin 1" if rabin else "Streett 1", formula([([0], [1])], rabin), 2, [[(0, 0, [1]), (0, 0, [0]), (1, 0, [])]]
        )
        with pytest.raises(NotImplementedError):
            parse_hoa(text)
        for cls in (PropDRA, PropDSA):
            with pytest.raises(HoaError, match="not deterministic"):
                cls.from_hoa(text)


def test_malformed_texts_are_hoa_errors():
    ok = hoa_text("Rabin 1", "(Fin(0)) & (Inf(1))", 2, [[(0, 0, [1]), (1, 0, [])]])
    assert PropDRA.from_hoa(ok).num_edges == 2
    for bad in ("", "garbage", ok.replace("--END--", ""), ok.replace("[0] 0", "[0] 7")):
        for cls in (PropDRA, PropDSA):
            with pytest.raises((HoaError, automata.AcceptanceError)):
                cls.from_hoa(bad)
        with pytest.raises(automata.Error):
            parse_hoa(bad)
