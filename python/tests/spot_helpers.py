"""Shared helpers of the differential tests against Spot (`test_spot_*.py`).

Importing this module skips the importing test module if Spot (`import spot`) or its command line
tool `randaut` is not available. Spot reads our results through `to_hoa()` and we read Spot's
through `automata.parse_hoa`; words travel as lassos `prefix cycle{period}`.
"""

import itertools
import pathlib
import random
import shutil

import pytest

spot = pytest.importorskip("spot")
if shutil.which("randaut") is None:
    pytest.skip("Spot's `randaut` is not on the PATH", allow_module_level=True)

import automata  # noqa: E402
from automata import OmegaWord  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURES = sorted((ROOT / "benches" / "fixtures").glob("**/*.hoa"))

# name -> (acceptance condition for randaut, class of `parse_hoa` if deterministic,
#          class of `parse_hoa` if not deterministic or None if the bindings have none)
KINDS = {
    "buchi": ("Buchi", "PropDBA", "PropNBA"),
    "cobuchi": ("Fin(0)", "PropDCA", "PropNCA"),
    "parity-min-even": ("parity min even 3", "PropDPA", "PropNPA"),
    "parity-max-even": ("parity max even 3", "PropDPAMaxEven", None),
    "parity-min-odd": ("parity min odd 3", "PropDPAMinOdd", None),
    "parity-max-odd": ("parity max odd 3", "PropDPAMaxOdd", None),
    "rabin": ("Rabin 2", "PropDRA", None),
    "streett": ("Streett 2", "PropDSA", None),
}
PARITY = [k for k in KINDS if k.startswith("parity")]
SEEDS = range(1, 7)


def randaut(kind, seed, deterministic, states=5, aps=2, density=None, acc_prob=None):
    """A random automaton of Spot (`randaut`); deterministic ones are complete."""
    cmd = f"randaut -Q{states} -A '{KINDS[kind][0]}' --seed={seed} {'-D' if deterministic else ''}"
    if density is not None:
        cmd += f" -e {density}"
    if acc_prob is not None:
        cmd += f" -a {acc_prob}"
    # randaut leaves edges without a parity color; our reader needs exactly one (see
    # `test_parity_edges_without_color_are_read`)
    colored = "--colored" if kind in PARITY else ""
    return spot.automaton(f"{cmd} {colored} {aps} |")


def expected_class(kind, spot_aut):
    """Name of the class `parse_hoa` returns for the random automaton (`randaut` without `-D`
    sometimes gives a deterministic one)."""
    return KINDS[kind][1 if spot.is_deterministic(spot_aut) else 2]


def widen(text, kind, seed):
    """HOA text of an automaton whose language contains the one of `text` (random changes of
    edges that can only add accepted words): Büchi edges get the mark, odd color 1 of min even
    parity (3 colors) becomes 2."""
    rng = random.Random(seed)
    lines = []
    for line in text.splitlines():
        if line.startswith("["):
            if kind == "buchi" and "{" not in line and rng.random() < 0.5:
                line += " {0}"
            elif kind == "parity-min-even" and line.endswith("{1}") and rng.random() < 0.5:
                line = line[:-3] + "{2}"
        lines.append(line)
    return "\n".join(lines) + "\n"


def case_id(kind, deterministic, seed):
    return f"{kind}-{'det' if deterministic else 'nondet'}-s{seed}"


def cases(kinds, deterministic=(True, False), seeds=SEEDS):
    """pytest parameters `(kind, deterministic, seed)` with readable ids; kinds without a class
    for the nondeterministic case are left out of it."""
    return [
        pytest.param(k, d, s, id=case_id(k, d, s))
        for k, d, s in itertools.product(kinds, deterministic, seeds)
        if d or KINDS[k][2] is not None
    ]


def hoa(spot_aut, fmt="t"):
    """HOA text of the Spot automaton; `t` forces transition-based acceptance, which is the only
    form our reader understands (see `test_state_based_acceptance_is_read`)."""
    return str(spot_aut.to_str("hoa", fmt))


def ours(spot_aut):
    """Our class for the Spot automaton."""
    return automata.parse_hoa(hoa(spot_aut))


def to_spot(our_aut):
    return spot.automaton(our_aut.to_hoa())


def msg(what, *auts):
    """Failure message with the HOA of every automaton involved (Spot's or ours)."""
    parts = [what]
    for i, a in enumerate(auts):
        text = a if isinstance(a, str) else hoa(a) if hasattr(a, "get_dict") else a.to_hoa()
        parts.append(f"--- input {i} (HOA) ---\n{text}")
    return "\n".join(parts)


def fixture_cases(max_states=None):
    """pytest parameters for the fixture files (optionally only those with few states)."""
    out = []
    for path in FIXTURES:
        n = int(next(l for l in path.read_text().splitlines() if l.startswith("States:")).split()[1])
        if max_states is None or n <= max_states:
            out.append(pytest.param(path, id=str(path.relative_to(ROOT / "benches" / "fixtures"))))
    return out


def read_fixture(path, split=False):
    """The fixture as `(spot automaton, our automaton)`; `split` splits edges into minterms
    (needed for inclusion, see `test_inclusion_of_automata_with_true_labels`)."""
    sa = spot.automaton(str(path))
    if split:
        sa = spot.split_edges(sa)
    return sa, ours(sa)


def lassos(num_aps, seed, count=25, max_prefix=3, max_period=3):
    """Pseudo-random ultimately periodic words over the propositional alphabet with `num_aps`
    propositions (letters are lists of booleans)."""
    rng = random.Random(seed)

    def letters(n):
        return [[rng.random() < 0.5 for _ in range(num_aps)] for _ in range(n)]

    return [
        OmegaWord(letters(rng.randint(0, max_prefix)), letters(rng.randint(1, max_period)))
        for _ in range(count)
    ]


def _letter(aps, letter):
    return " & ".join(ap if bit else f"!{ap}" for ap, bit in zip(aps, letter))


def spot_word(spot_aut, word, aps):
    """Our `OmegaWord` over `aps` as a Spot word, in the dictionary of `spot_aut`."""
    prefix = "".join(_letter(aps, a) + "; " for a in word.prefix)
    cycle = "; ".join(_letter(aps, a) for a in word.period)
    return spot.parse_word(f"{prefix}cycle{{{cycle}}}", spot_aut.get_dict())


def spot_accepts(spot_aut, word, aps):
    return spot_aut.intersects(spot_word(spot_aut, word, aps).as_automaton())


def cap(aut, max_states):
    """Skips the test if the (Spot or our) automaton is too big for a slow check."""
    n = aut.num_states() if hasattr(aut, "get_dict") else aut.num_states
    if n > max_states:
        pytest.skip(f"{n} states > {max_states}")
