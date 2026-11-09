"""Emptiness, witnesses and `accepts` against Spot."""

import pytest
from spot_helpers import *  # noqa: F403  (also skips this module without Spot)

pytestmark = pytest.mark.spot


def check_emptiness_and_witness(a, o):
    aps = o.alphabet.aps
    assert o.is_empty() == a.is_empty(), msg(f"is_empty: ours {o.is_empty()}, Spot {a.is_empty()}", a)
    w = o.accepting_word()
    if a.is_empty():
        assert w is None, msg(f"Spot says empty, we found the word {w!r}", a)
    else:
        assert w is not None, msg("not empty in Spot, but no accepting word", a)
        assert o.accepts(w), msg(f"our accepting word {w!r} is not accepted by us", a)
        assert spot_accepts(a, w, aps), msg(f"our accepting word {w!r} is rejected by Spot", a)


def check_accepts(a, o, seed):
    aps = o.alphabet.aps
    for w in lassos(len(aps), seed):
        ours_, theirs = o.accepts(w), spot_accepts(a, w, aps)
        assert ours_ == theirs, msg(f"accepts({w.prefix!r} {w.period!r}^w): ours {ours_}, Spot {theirs}", a)


@pytest.mark.parametrize(("kind", "det", "seed"), cases(KINDS, seeds=range(1, 25)))
def test_random_automaton_emptiness_and_witness(kind, det, seed):
    # the density and the share of marked edges vary, so that both empty and non-empty ones occur
    a = randaut(kind, seed, det, states=6, density=[0.15, 0.6][seed % 2], acc_prob=[0.05, 0.5, 0.95][seed % 3])
    try:
        o = ours(a)
    except NotImplementedError:
        pytest.skip("no class for this nondeterministic automaton")
    check_emptiness_and_witness(a, o)


@pytest.mark.parametrize(("kind", "det", "seed"), cases(KINDS))
def test_random_automaton_accepts_lassos(kind, det, seed):
    a = randaut(kind, seed, det)
    try:
        o = ours(a)
    except NotImplementedError:
        pytest.skip("no class for this nondeterministic automaton")
    check_accepts(a, o, seed)


@pytest.mark.parametrize("path", fixture_cases())
def test_fixture_emptiness_and_witness(path):
    check_emptiness_and_witness(*read_fixture(path))


@pytest.mark.parametrize("path", fixture_cases())
def test_fixture_accepts_lassos(path):
    check_accepts(*read_fixture(path), seed=len(path.name))
