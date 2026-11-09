"""Automata built with our constructors, written with `to_hoa()` and read by Spot: the language
(emptiness and many lassos) must be the same on both sides."""

import itertools
import random

import pytest
from spot_helpers import *  # noqa: F403  (also skips this module without Spot)

pytestmark = pytest.mark.spot

APS = ["a", "b"]
SYMBOLS = [list(v) for v in itertools.product([False, True], repeat=len(APS))]
PAIRS = [([0], [1]), ([2], [3])]  # the only pairs `to_hoa` of a DRA/DSA can be read back with
# class name -> (color generator, constructor arguments after the edges, deterministic)
CLASSES = {
    "PropDBA": (lambda r: r.random() < 0.3, (), True),
    "PropDCA": (lambda r: r.random() < 0.3, (), True),
    "PropDPA": (lambda r: r.randint(0, 3), (), True),
    "PropDPAMaxEven": (lambda r: r.randint(0, 3), (), True),
    "PropDPAMinOdd": (lambda r: r.randint(0, 3), (), True),
    "PropDPAMaxOdd": (lambda r: r.randint(0, 3), (), True),
    "PropDRA": (lambda r: r.randint(0, 3), (PAIRS,), True),
    "PropDSA": (lambda r: r.randint(0, 3), (PAIRS,), True),
    "PropNBA": (lambda r: r.random() < 0.3, (), False),
    "PropNCA": (lambda r: r.random() < 0.3, (), False),
    "PropNPA": (lambda r: r.randint(0, 3), (), False),
}


def build(name, seed):
    color, extra, deterministic = CLASSES[name]
    rng = random.Random(seed)
    n = rng.randint(1, 5)
    edges = []
    for q in range(n):
        for sym in SYMBOLS:
            for t in rng.sample(range(n), 1 if deterministic else rng.randint(1, min(n, 2))):
                edges.append((q, sym, color(rng), t))
    return getattr(automata, name)(automata.PropAlphabet(APS), n, 0, edges, *extra)


@pytest.mark.parametrize("seed", range(1, 21))
@pytest.mark.parametrize("name", CLASSES)
def test_constructed_automaton_agrees_with_spot(name, seed):
    o = build(name, seed)
    text = o.to_hoa()
    sa = spot.automaton(text)
    assert o.is_empty() == sa.is_empty(), msg("is_empty differs from Spot", text)
    for w in lassos(len(APS), seed, count=20):
        assert o.accepts(w) == spot_accepts(sa, w, APS), msg(f"accepts({w.prefix!r} {w.period!r}^w) differs from Spot", text)
    back = automata.parse_hoa(text)
    assert spot.are_equivalent(sa, to_spot(back)), msg("our own HOA does not survive a read", text)
