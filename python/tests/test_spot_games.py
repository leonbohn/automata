"""Winning regions of parity games against `spot.solve_parity_game` (PGSolver format, max-even)."""

import random

import pytest
from spot_helpers import *  # noqa: F403  (also skips this module without Spot)

import automata

pytestmark = pytest.mark.spot


def random_game(seed):
    rng = random.Random(seed)
    n = rng.randint(1, 30)
    lines = [f"parity {n - 1};"]
    for v in range(n):
        succ = sorted({rng.randrange(n) for _ in range(rng.randint(1, 3))})
        lines.append(f"{v} {rng.randrange(7)} {rng.randrange(2)} {','.join(map(str, succ))};")
    return "\n".join(lines) + "\n"


@pytest.mark.parametrize("seed", range(1, 101))
def test_winning_regions(seed, tmp_path):
    text = random_game(seed)
    path = tmp_path / "game.pg"
    path.write_text(text)
    theirs = spot.automaton(str(path))
    spot.solve_parity_game(theirs, True)  # for all vertices, not only the initial one
    # Spot's player 1 is Adam (the odd player)
    expected = ["adam" if odd else "eve" for odd in spot.get_state_winners(theirs)]
    assert automata.MaxEvenParityGame.from_pgsolver(text).solve() == expected, text
