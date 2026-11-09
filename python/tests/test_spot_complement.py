"""Complements against `spot.dualize` (the automata are deterministic and complete)."""

import pytest
from spot_helpers import *  # noqa: F403  (also skips this module without Spot)

pytestmark = pytest.mark.spot


def check_complement(sa, o, seed):
    """`o.complement()` is the dual of `sa`: equivalent to `spot.dualize`, disjoint from it and
    agreeing with Spot on lassos."""
    if not hasattr(o, "complement"):
        pytest.skip(f"{type(o).__name__} has no complement yet")
    c = o.complement()
    sc = to_spot(c)
    assert not sa.intersects(sc), msg("complement intersects the automaton", sa, c)
    assert spot.are_equivalent(sc, spot.dualize(sa)), msg("complement differs from spot.dualize", sa, c)
    aps = o.alphabet.aps
    for w in lassos(len(aps), seed, count=10):
        assert c.accepts(w) != spot_accepts(sa, w, aps), msg(f"complement on {w.prefix!r} {w.period!r}^w", sa, c)


@pytest.mark.parametrize(("kind", "det", "seed"), cases(KINDS, deterministic=(True,)))
def test_random_complement(kind, det, seed):
    sa = randaut(kind, seed, True)
    check_complement(sa, ours(sa), seed)


@pytest.mark.parametrize("path", fixture_cases(max_states=130))
def test_fixture_complement(path):
    sa, o = read_fixture(path)
    check_complement(sa, o, len(path.name))
