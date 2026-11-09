"""Every class can be written as DOT and drawn as SVG."""

import pytest

from automata import (
    DBA, DCA, DFA, DMA, DPA, DRA, DSA, NBA, NCA, NFA, NPA, CharAlphabet, DPAMaxEven,
    DPAMaxOdd, DPAMinOdd, MealyMachine, MooreMachine,
)

AB = CharAlphabet("ab")
LOOP = [(0, "a", 0, 0), (0, "b", 1, 0)]
BOOL_LOOP = [(0, "a", True, 0), (0, "b", False, 0)]


def instances():
    return {
        "DFA": DFA(AB, 1, 0, [0], [(0, "a", 0), (0, "b", 0)]),
        "DBA": DBA(AB, 1, 0, BOOL_LOOP),
        "DCA": DCA(AB, 1, 0, BOOL_LOOP),
        "DPA": DPA(AB, 1, 0, LOOP),
        "DPAMaxEven": DPAMaxEven(AB, 1, 0, LOOP),
        "DPAMinOdd": DPAMinOdd(AB, 1, 0, LOOP),
        "DPAMaxOdd": DPAMaxOdd(AB, 1, 0, LOOP),
        "DRA": DRA(AB, 1, 0, LOOP, [([0], [1])]),
        "DSA": DSA(AB, 1, 0, LOOP, [([0], [1])]),
        "DMA": DMA(AB, 1, 0, LOOP, [[0, 1]]),
        "NFA": NFA.from_dfa(DFA(AB, 1, 0, [0], [(0, "a", 0), (0, "b", 0)])),
        "NBA": NBA.from_dba(DBA(AB, 1, 0, BOOL_LOOP)),
        "NCA": NCA.from_dca(DCA(AB, 1, 0, BOOL_LOOP)),
        "NPA": NPA.from_dpa(DPA(AB, 1, 0, LOOP)),
    }


@pytest.mark.parametrize("name", list(instances()))
def test_dot_and_svg(name):
    aut = instances()[name]
    dot = aut.to_dot()
    assert dot.startswith("digraph") and "init -> q0" in dot
    assert "<svg" in aut._repr_svg_()


def test_conditions_are_part_of_the_drawing():
    assert "Rabin: (fin {0}, inf {1})" in instances()["DRA"].to_dot()
    assert "Streett: (fin {0}, inf {1})" in instances()["DSA"].to_dot()
    assert "Muller: [0, 1]" in instances()["DMA"].to_dot()
    assert "Rabin" in instances()["DRA"]._repr_svg_()
    assert "doublecircle" in instances()["NFA"].to_dot()
    assert 'label="a|0"' in instances()["NPA"].to_dot()


def test_machines_still_have_dot():
    moore = MooreMachine(AB, [3], 0, [(0, "a", 0), (0, "b", 0)])
    mealy = MealyMachine(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 2, 0)])
    assert moore.to_dot().startswith("digraph") and "<svg" in moore._repr_svg_()
    assert mealy.to_dot().startswith("digraph") and "<svg" in mealy._repr_svg_()
