import pytest

import automata
from automata import (
    GameError,
    MaxEvenParityGame,
    MaxOddParityGame,
    MinEvenParityGame,
    MinOddParityGame,
)

# vertex i: (owner, priority); the game is the example of the lecture "Infinite Computation and
# Games" (Löding) with max-even priorities
OWNERS = ["eve", "adam", "adam", "adam", "adam", "eve", "adam", "eve"]
PRIORITIES = [3, 2, 2, 3, 2, 0, 4, 1]
EDGES = [(0, 1), (0, 4), (1, 0), (1, 2), (1, 5), (2, 3), (2, 5), (3, 7),
         (4, 0), (4, 5), (5, 1), (5, 2), (6, 2), (6, 7), (7, 6), (7, 3)]  # fmt: skip
WINNERS = ["adam", "adam", "eve", "eve", "adam", "eve", "eve", "eve"]


def lecture(cls, priorities):
    return cls(list(zip(OWNERS, priorities)), EDGES)


def test_all_conditions_agree():
    # the same plays are won by Eve if the priorities are rewritten for the condition
    assert lecture(MaxEvenParityGame, PRIORITIES).solve() == WINNERS
    assert lecture(MaxOddParityGame, [p + 1 for p in PRIORITIES]).solve() == WINNERS
    assert lecture(MinEvenParityGame, [6 - p for p in PRIORITIES]).solve() == WINNERS
    assert lecture(MinOddParityGame, [7 - p for p in PRIORITIES]).solve() == WINNERS


def test_incremental_construction():
    game = MaxEvenParityGame()
    assert len(game) == 0
    v = game.add_vertex("eve", 2)
    w = game.add_vertex("adam", 1)
    game.add_edge(v, w)
    game.add_edge(w, w)
    assert len(game) == 2
    assert game.solve() == ["adam", "adam"]


def test_not_total():
    game = MaxEvenParityGame([("eve", 0)])
    with pytest.raises(GameError):
        game.solve()
    with pytest.raises(automata.Error):
        game.solve()


def test_invalid_input():
    game = MaxEvenParityGame([("eve", 0)])
    with pytest.raises(ValueError):
        game.add_vertex("nobody", 0)
    with pytest.raises(ValueError):
        game.add_edge(0, 1)
    with pytest.raises(ValueError):
        MaxEvenParityGame([("eve", 0)], [(1, 0)])
    with pytest.raises(OverflowError):
        game.add_vertex("eve", 256)


def test_pgsolver_roundtrip():
    game = lecture(MaxEvenParityGame, PRIORITIES)
    text = game.to_pgsolver()
    assert text.startswith("parity 7;\n0 3 0 1,4;\n")
    read = MaxEvenParityGame.from_pgsolver(text)
    assert read.to_pgsolver() == text
    assert read.solve() == WINNERS
    # the format has no condition, the class decides what the priorities mean
    assert MinOddParityGame.from_pgsolver(text).solve() == lecture(MinOddParityGame, PRIORITIES).solve()


def test_pgsolver_invalid():
    with pytest.raises(GameError):
        MaxEvenParityGame.from_pgsolver("0 0 2 0;")


def test_solve_zielonka_agrees():
    game = lecture(MaxEvenParityGame, PRIORITIES)
    assert game.solve_zielonka() == game.solve() == WINNERS


def test_strategy_stays_in_winning_region():
    game = lecture(MaxEvenParityGame, PRIORITIES)
    winners, strategy = game.solve_with_strategy()
    assert winners == WINNERS
    for v, (owner, w) in enumerate(zip(OWNERS, strategy)):
        if owner == winners[v]:
            assert (v, w) in EDGES and winners[w] == winners[v]
        else:
            assert w is None


def test_letter_game_decides_universality():
    a = automata.CharAlphabet("ab")
    universal = automata.DPA(a, 1, 0, [(0, "a", 0, 0), (0, "b", 2, 0)])
    other = automata.DPA(a, 1, 0, [(0, "a", 0, 0), (0, "b", 1, 0)])
    for dpa, winner in [(universal, "eve"), (other, "adam")]:
        game, initial = dpa.letter_game()
        assert game.solve()[initial] == winner
