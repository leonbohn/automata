"""Conversions, normal forms and `rejected_word` against Spot."""

import pytest
from spot_helpers import *  # noqa: F403  (also skips this module without Spot)

pytestmark = pytest.mark.spot


def check_equivalent(sa, result):
    assert spot.are_equivalent(sa, to_spot(result)), msg(f"{type(result).__name__} is not equivalent to the source", sa, result)


@pytest.mark.parametrize(("kind", "cls", "target"), [
    ("buchi", "PropDPA", "from_dba"), ("cobuchi", "PropDPA", "from_dca"),
    ("buchi", "PropNBA", "from_dba"), ("cobuchi", "PropNCA", "from_dca"),
    ("parity-min-even", "PropNPA", "from_dpa"),
])
@pytest.mark.parametrize("seed", SEEDS)
def test_embedding_of_a_simpler_condition(kind, cls, target, seed):
    sa = randaut(kind, seed, True)
    check_equivalent(sa, getattr(getattr(automata, cls), target)(ours(sa)))


@pytest.mark.parametrize("kind", PARITY)
@pytest.mark.parametrize("seed", SEEDS)
def test_to_min_even(kind, seed):
    sa = randaut(kind, seed, True)
    o = ours(sa)
    if kind != "parity-min-even":
        o = o.to_min_even()
    check_equivalent(sa, o)


@pytest.mark.parametrize("method", ["normalized", "streamlined"])
@pytest.mark.parametrize("seed", SEEDS)
def test_normal_forms_of_random_dpas(method, seed):
    sa = randaut("parity-min-even", seed, True, states=6)
    check_equivalent(sa, getattr(ours(sa), method)())


@pytest.mark.parametrize("method", ["normalized", "streamlined"])
@pytest.mark.parametrize("path", fixture_cases(max_states=130))
def test_normal_forms_of_fixtures(method, path):
    sa, o = read_fixture(path)
    check_equivalent(sa, getattr(o, method)())


@pytest.mark.parametrize("seed", range(1, 25))
def test_rejected_word(seed):
    sa = randaut("parity-min-even", seed, True, states=6, density=[0.15, 0.6][seed % 2], acc_prob=[0.05, 0.5, 0.95][seed % 3])
    o = ours(sa)
    w = o.rejected_word()
    if spot.dualize(sa).is_empty():
        assert w is None, msg(f"the automaton is universal in Spot, but we found {w!r}", sa)
    else:
        if w is None:
            pytest.xfail("BUG: rejected_word is None for a non-universal DPA, see `test_rejected_word_is_found`")
        assert not o.accepts(w) and not spot_accepts(sa, w, o.alphabet.aps), msg(f"{w!r} is accepted", sa)


@pytest.mark.xfail(
    strict=True,
    reason="BUG: `DPA::give_rejected_word` (src/automaton/omega/parity.rs) finds no word although the "
    "complement accepts a^w (the loop of color 1 is only reachable through an edge of color 0)",
)
def test_rejected_word_is_found():
    ab = automata.CharAlphabet("ab")
    d = automata.DPA(ab, 2, 0, [(0, "a", 0, 1), (0, "b", 0, 1), (1, "b", 2, 0), (1, "a", 1, 1)])
    assert not d.accepts(automata.OmegaWord("", "a"))
    assert d.rejected_word() is not None
