"""Finite words are not comparable to Spot, so `DFA.minimize` and `NFA.determinize` are checked
against naive Python implementations (no Spot needed)."""

import itertools
import random

import pytest

from automata import DFA, NFA, CharAlphabet

AB = CharAlphabet("ab")
WORDS = ["".join(w) for n in range(8) for w in itertools.product("ab", repeat=n)]


def random_dfa(seed):
    rng = random.Random(seed)
    n = rng.randint(1, 9)
    edges = [(q, s, rng.randrange(n)) for q in range(n) for s in "ab"]
    return DFA(AB, n, 0, [q for q in range(n) if rng.random() < 0.4], edges), n, edges


def random_nfa(seed):
    rng = random.Random(seed)
    n = rng.randint(1, 6)
    edges = [(q, s, t) for q in range(n) for s in "ab" for t in range(n) if rng.random() < 0.25]
    return NFA(AB, n, 0, [q for q in range(n) if rng.random() < 0.4], edges)


def moore_classes(dfa, n, edges, only_reachable):
    """Number of classes of Moore's partition refinement (of the states reachable from 0 or of
    all states)."""
    delta = {(q, s): t for q, s, t in edges}
    states, todo = ({0}, [0]) if only_reachable else (set(range(n)), [])
    while todo:
        q = todo.pop()
        for s in "ab":
            if delta[q, s] not in states:
                states.add(delta[q, s])
                todo.append(delta[q, s])
    block = {q: dfa.is_accepting(q) for q in states}
    while True:
        ids = {}
        refined = {q: ids.setdefault((block[q], block[delta[q, "a"]], block[delta[q, "b"]]), len(ids)) for q in states}
        if len(ids) == len(set(block.values())):
            return len(ids)
        block = refined


@pytest.mark.parametrize("seed", range(60))
def test_minimize_matches_moore_partition_refinement(seed):
    dfa, n, edges = random_dfa(seed)
    minimal = dfa.minimize()
    # unreachable states are merged with each other (and with reachable ones) but not removed
    assert minimal.num_states == moore_classes(dfa, n, edges, only_reachable=False), edges
    assert all(minimal.accepts(w) == dfa.accepts(w) for w in WORDS), f"language changed: {edges}"
    assert minimal.minimize().num_states == minimal.num_states


@pytest.mark.xfail(
    strict=True,
    reason="DOC MISMATCH: `DFA.minimize` is documented as 'the minimal DFA' but keeps unreachable states",
)
def test_minimize_removes_unreachable_states():
    dfa = DFA(AB, 3, 0, [0], [(0, "a", 0), (0, "b", 0), (1, "a", 2), (1, "b", 1), (2, "a", 1), (2, "b", 1)])
    assert dfa.minimize().num_states == 1


@pytest.mark.parametrize("seed", range(60))
def test_determinize_preserves_the_language_up_to_length_7(seed):
    nfa = random_nfa(seed)
    dfa = nfa.determinize()
    wrong = [w for w in WORDS if nfa.accepts(w) != dfa.accepts(w)]
    assert not wrong, f"determinize differs on {wrong[:3]}; NFA {nfa!r}"
