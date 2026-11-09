"""Inclusion and equivalence of DBAs and DPAs (with counterexamples) against Spot."""

import pytest
from spot_helpers import *  # noqa: F403  (also skips this module without Spot)

pytestmark = pytest.mark.spot

KINDS_WITH_INCLUSION = ["buchi", "parity-min-even"]


def pairs(kind):
    """`(id, spot A, spot B)`: independent random automata, B a widening of A (A is included in
    B, mostly strictly), and B an equivalent but structurally different version of A."""
    out = []
    for seed in range(1, 9):
        a = randaut(kind, seed, True, states=4)
        out.append((f"random-s{seed}", a, randaut(kind, seed + 100, True, states=4)))
        text = hoa(a)
        out.append((f"widened-s{seed}", a, spot.automaton(widen(text, kind, seed))))
        cleaned = spot.scc_filter(a)
        out.append((f"cleaned-s{seed}", a, spot.colorize_parity(cleaned, True) if kind in PARITY else cleaned))
    return out


def params():
    return [pytest.param(k, a, b, id=f"{k}-{i}") for k in KINDS_WITH_INCLUSION for i, a, b in pairs(k)]


@pytest.mark.parametrize(("kind", "sa", "sb"), params())
def test_inclusion_and_equivalence_agree_with_spot(kind, sa, sb):
    # edges are split into minterms: inclusion is wrong for edges with the label `t`, see
    # `test_inclusion_of_automata_with_true_labels`
    sa, sb = spot.split_edges(sa), spot.split_edges(sb)
    try:
        a, b = ours(sa), ours(sb)
    except (automata.HoaError, NotImplementedError):
        pytest.skip("Spot simplified the automaton to acceptance `all`, which has no class")
    aps = a.alphabet.aps
    both = msg("", sa, sb)

    included = spot.contains(sb, sa)  # L(sa) is a subset of L(sb)
    assert a.included_in(b) == included, f"included_in: Spot says {included}{both}"
    cex = a.inclusion_counterexample(b)
    assert (cex is None) == included, f"inclusion_counterexample {cex!r}, Spot says included={included}{both}"
    if cex is not None:
        assert spot_accepts(sa, cex, aps) and not spot_accepts(sb, cex, aps), (
            f"inclusion counterexample {cex!r} is not in L(A) minus L(B) in Spot{both}"
        )

    equivalent = spot.are_equivalent(sa, sb)
    assert a.equivalent_to(b) == equivalent, f"equivalent_to: Spot says {equivalent}{both}"
    cex = a.equivalence_counterexample(b)
    assert (cex is None) == equivalent, f"equivalence_counterexample {cex!r}, Spot says equivalent={equivalent}{both}"
    if cex is not None:
        assert spot_accepts(sa, cex, aps) != spot_accepts(sb, cex, aps), (
            f"equivalence counterexample {cex!r} is accepted by both or neither in Spot{both}"
        )


def ap_line(path):
    return next(l for l in path.read_text().splitlines() if l.startswith("AP:"))


def fixture_pairs():
    """Each fixture (at most 64 states) with the next one over the same propositions."""
    out = []
    for i, path in enumerate(FIXTURES):
        for other in FIXTURES[i + 1 :] + FIXTURES[:i]:
            if ap_line(other) == ap_line(path):
                out.append(pytest.param(path, other, id=f"{path.stem}-{other.stem}"))
                break
    return out


@pytest.mark.parametrize(("path", "other"), fixture_pairs())
def test_fixture_is_equivalent_to_its_normalization_and_compares_with_a_neighbor(path, other):
    sa, a = read_fixture(path, split=True)
    sb, b = read_fixture(other, split=True)
    cap(a, 300), cap(b, 300)
    assert a.equivalent_to(a.normalized()) and a.equivalence_counterexample(a.streamlined()) is None
    assert a.equivalent_to(b) == spot.are_equivalent(sa, sb), msg("equivalent_to differs from Spot", sa, sb)
    assert a.included_in(b) == spot.contains(sb, sa), msg("included_in differs from Spot", sa, sb)


HOA_BUCHI = """HOA: v1
States: 2
Start: 0
AP: 1 "p0"
acc-name: Buchi
Acceptance: 1 Inf(0)
--BODY--
{}
--END--
"""


def test_inclusion_of_automata_with_true_labels():
    a = automata.parse_hoa(HOA_BUCHI.format("State: 0\n[t] 1 {0}\nState: 1\n[0] 0\n[!0] 1"))
    b = automata.parse_hoa(HOA_BUCHI.format("State: 0\n[t] 1\nState: 1\n[t] 0"))
    assert not a.is_empty() and b.is_empty()
    assert not a.included_in(b)
