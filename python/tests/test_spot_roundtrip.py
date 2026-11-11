"""HOA round trip: Spot's HOA -> `parse_hoa` -> `to_hoa` -> Spot, the language must not change."""

import pytest
from spot_helpers import *  # noqa: F403  (also skips this module without Spot)

pytestmark = pytest.mark.spot


@pytest.mark.parametrize(("kind", "det", "seed"), cases(KINDS))
def test_random_automaton_round_trips(kind, det, seed):
    a = randaut(kind, seed, det)
    o = ours(a)
    assert type(o).__name__ == expected_class(kind, a), msg("class", a)
    b = to_spot(o)
    assert spot.are_equivalent(a, b), msg("round trip changed the language", a, o)


@pytest.mark.parametrize("kind", [k for k in KINDS if KINDS[k][2] is None])
def test_nondeterministic_automata_without_a_class_raise(kind):
    a = randaut(kind, 1, False)
    assert not spot.is_deterministic(a)
    with pytest.raises(NotImplementedError):
        ours(a)


@pytest.mark.parametrize("path", fixture_cases(max_states=300))
def test_fixture_round_trips(path):
    a, o = read_fixture(path)
    assert type(o).__name__ == "PropDPA"
    assert spot.are_equivalent(a, to_spot(o)), msg("round trip changed the language", a)


def test_state_based_acceptance_is_read():
    a = randaut("buchi", 5, True)
    text = hoa(a, "s")
    assert "State: 0 {0}" in text
    o = automata.parse_hoa(text)
    assert spot.are_equivalent(a, to_spot(o)), msg("state-based acceptance lost", text)


def test_parity_edges_without_color_are_read():
    a = spot.automaton("randaut -Q5 -A 'parity min even 3' --seed=1 -D 2 |")
    o = automata.parse_hoa(hoa(a))
    assert spot.are_equivalent(a, to_spot(o))
