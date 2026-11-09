"""HOA input/output, conversions between classes, and DOT/SVG output."""

import pytest

import automata
from automata import (
    DBA,
    DCA,
    DFA,
    DPA,
    NBA,
    NCA,
    NFA,
    NPA,
    CharAlphabet,
    HoaError,
    MealyMachine,
    MooreMachine,
    OmegaWord,
    PropAlphabet,
    PropDBA,
    PropDCA,
    PropDFA,
    PropDPA,
    PropNBA,
    PropNCA,
    PropNPA,
    parse_hoa,
    parse_hoa_all,
)

AB = CharAlphabet("ab")
P = PropAlphabet(["p"])
T, F = [True], [False]

# "infinitely many a": Büchi on the color of the edge reading a
DBA_TEXT = """HOA: v1
States: 1
Start: 0
acc-name: Buchi
Acceptance: 1 Inf(0)
AP: 1 "p"
--BODY--
State: 0
[0] 0 {0}
[!0] 0
--END--
"""

DPA_TEXT = """HOA: v1
States: 1
Start: 0
acc-name: parity min even 2
Acceptance: 2 Inf(0) | Fin(1)
AP: 1 "p"
--BODY--
State: 0
[0] 0 {0}
[!0] 0 {1}
--END--
"""

# parity max even: the largest color seen infinitely often has to be even
MAX_DPA_TEXT = """HOA: v1
States: 1
Start: 0
acc-name: parity max even 3
Acceptance: 3 Inf(2) | (Fin(1) & Inf(0))
AP: 1 "p"
--BODY--
State: 0
[0] 0 {2}
[!0] 0 {1}
--END--
"""

# nondeterministic: guesses the point after which only p is read
NBA_TEXT = """HOA: v1
States: 2
Start: 0
acc-name: Buchi
Acceptance: 1 Inf(0)
AP: 1 "p"
--BODY--
State: 0
[t] 0
[0] 1
State: 1
[0] 1 {0}
--END--
"""

NPA_TEXT = """HOA: v1
States: 2
Start: 0
acc-name: parity min even 2
Acceptance: 2 Inf(0) | Fin(1)
AP: 1 "p"
--BODY--
State: 0
[t] 0 {1}
[0] 1 {1}
State: 1
[0] 1 {0}
--END--
"""

RABIN_TEXT = """HOA: v1
States: 1
Start: 0
acc-name: Rabin 1
Acceptance: 2 Fin(0) & Inf(1)
AP: 1 "p"
--BODY--
State: 0
[0] 0 {1}
[!0] 0 {0}
--END--
"""

# nondeterministic: two edges for `p`
NRA_TEXT = RABIN_TEXT.replace("[0] 0 {1}", "[t] 0 {1}")

WORDS = [
    OmegaWord([], [T]),
    OmegaWord([], [F]),
    OmegaWord([], [T, F]),
    OmegaWord([T, T], [F]),
    OmegaWord([F, F], [T]),
]


def verdicts(aut):
    return [aut.accepts(w) for w in WORDS]


def test_from_hoa_reads_every_supported_class():
    assert verdicts(PropDBA.from_hoa(DBA_TEXT)) == [True, False, True, False, True]
    assert verdicts(PropDPA.from_hoa(DPA_TEXT)) == [True, False, True, False, True]
    assert verdicts(PropNBA.from_hoa(NBA_TEXT)) == [True, False, False, False, True]
    assert verdicts(PropNPA.from_hoa(NPA_TEXT)) == [True, False, False, False, True]


def test_from_hoa_reads_the_number_of_states_and_the_initial_state():
    a = PropDBA.from_hoa(NBA_TEXT.replace("[t] 0\n[0] 1\nState: 1\n[0] 1 {0}", "[0] 1\nState: 1\n[0] 1 {0}"))
    assert (a.num_states, a.initial) == (2, 0)


def test_nondeterministic_classes_also_read_deterministic_text():
    assert verdicts(PropNBA.from_hoa(DBA_TEXT)) == verdicts(PropDBA.from_hoa(DBA_TEXT))
    assert verdicts(PropNPA.from_hoa(DPA_TEXT)) == verdicts(PropDPA.from_hoa(DPA_TEXT))


def test_deterministic_classes_reject_nondeterministic_text():
    with pytest.raises(HoaError, match="not deterministic"):
        PropDBA.from_hoa(NBA_TEXT)
    with pytest.raises(HoaError):
        PropDPA.from_hoa(NPA_TEXT)


def test_wrong_acceptance_condition_is_a_hoa_error():
    with pytest.raises(HoaError, match="Büchi"):
        PropDBA.from_hoa(DPA_TEXT)
    with pytest.raises(HoaError):
        PropNBA.from_hoa(DPA_TEXT)
    with pytest.raises(HoaError, match="parity"):
        PropNPA.from_hoa(DBA_TEXT)
    with pytest.raises(HoaError):
        PropNPA.from_hoa(NBA_TEXT)


def test_nondeterministic_max_and_odd_parity_are_not_implemented():
    for text in (MAX_DPA_TEXT, DPA_TEXT.replace("min even", "min odd")):
        with pytest.raises(NotImplementedError):
            PropNPA.from_hoa(text)
        nondeterministic = text.replace("State: 0\n", "State: 0\n[t] 0 {1}\n")
        with pytest.raises(NotImplementedError):
            parse_hoa(nondeterministic)


def test_rabin_is_only_read_by_the_rabin_class():
    with pytest.raises(NotImplementedError):
        PropDPA.from_hoa(RABIN_TEXT)
    with pytest.raises(NotImplementedError):
        PropNPA.from_hoa(RABIN_TEXT)
    with pytest.raises(NotImplementedError):
        parse_hoa(NRA_TEXT)
    with pytest.raises(HoaError):
        PropDBA.from_hoa(RABIN_TEXT)


@pytest.mark.parametrize(
    "text",
    [
        "",
        "garbage",
        "HOA: v1\n--BODY--\n--END--\n",
        DBA_TEXT.replace("--END--", ""),
        DBA_TEXT.replace("Start: 0", "Start: 0\nStart: 0"),
        DBA_TEXT.replace("[0] 0 {0}", "[0] 5 {0}"),
        DBA_TEXT.replace("States: 1\n", "").replace("[0] 0 {0}", "[0] 5 {0}"),
        DBA_TEXT.replace("States: 1\n", "").replace("Start: 0", "Start: 5"),
        DBA_TEXT.replace("State: 0", "State: 3"),
        DBA_TEXT.replace('AP: 1 "p"', 'AP: 1 "p" "q"'),
        DBA_TEXT.replace("AP: 1", "AP: 100"),
        DBA_TEXT.replace("[0] 0 {0}", "[0 &] 0 {0}"),
        DBA_TEXT.replace("[0] 0 {0}", "[7] 0 {0}"),
        DPA_TEXT.replace("{1}", "{9}"),
        DPA_TEXT.replace("{1}", ""),
        "\x00\x01--BODY--\n--END--",
        "--BODY--" * 1000 + "--END--",
    ],
)
def test_malformed_hoa_raises_hoa_error(text):
    for cls in (PropDBA, PropDPA, PropNBA, PropNPA):
        # an edge without a parity color is an AcceptanceError, which is not a HoaError
        with pytest.raises((HoaError, automata.AcceptanceError)):
            cls.from_hoa(text)
    with pytest.raises(automata.Error):
        parse_hoa(text)
    with pytest.raises(automata.Error):
        parse_hoa_all(text)


def test_parse_hoa_returns_the_most_specific_class():
    assert type(parse_hoa(DBA_TEXT)) is PropDBA
    assert type(parse_hoa(DPA_TEXT)) is PropDPA
    assert type(parse_hoa(NBA_TEXT)) is PropNBA
    assert type(parse_hoa(NPA_TEXT)) is PropNPA
    assert verdicts(parse_hoa(NPA_TEXT)) == verdicts(PropNPA.from_hoa(NPA_TEXT))


def test_parse_hoa_takes_the_first_automaton_and_parse_hoa_all_all_of_them():
    text = DBA_TEXT + "\n" + NBA_TEXT + DPA_TEXT
    assert type(parse_hoa(text)) is PropDBA
    assert [type(a) for a in parse_hoa_all(text)] == [PropDBA, PropNBA, PropDPA]
    assert [type(a) for a in parse_hoa_all(DBA_TEXT)] == [PropDBA]


def test_parse_hoa_all_fails_if_one_automaton_is_unsupported():
    with pytest.raises(NotImplementedError):
        parse_hoa_all(DBA_TEXT + NRA_TEXT)
    with pytest.raises(HoaError):
        parse_hoa_all(DBA_TEXT + "HOA: v1\n--BODY--\nState: 7\n--END--\n")


def test_to_hoa_round_trips_through_the_prop_classes():
    # reading a character automaton gives a one-hot encoding over the propositions "a" and "b"
    d = DBA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)])
    text = d.to_hoa()
    assert text.startswith("HOA: v1") and "acc-name: Buchi" in text and text.rstrip().endswith("--END--")
    back = PropDBA.from_hoa(text)
    assert back.num_states == 1 and back.num_edges == 2
    # only a, only b
    assert back.accepts(OmegaWord([], [[True, False]]))
    assert not back.accepts(OmegaWord([], [[False, True]]))
    assert parse_hoa(text).to_hoa() == back.to_hoa()


def test_to_hoa_of_prop_automata_is_stable():
    for cls, text in [
        (PropDBA, DBA_TEXT),
        (PropDPA, DPA_TEXT),
        (PropNBA, NBA_TEXT),
        (PropNPA, NPA_TEXT),
    ]:
        aut = cls.from_hoa(text)
        again = cls.from_hoa(aut.to_hoa())
        assert verdicts(again) == verdicts(aut)
        # the order of the edges of a state may change
        assert sorted(again.to_hoa().splitlines()) == sorted(aut.to_hoa().splitlines())


def test_to_hoa_of_character_automata():
    dpa = DPA(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 0, 0)])
    assert "acc-name: parity min even" in dpa.to_hoa()
    nba = NBA(AB, 2, 0, [(0, "a", False, 0), (0, "b", False, 1), (1, "b", True, 1)])
    assert "acc-name: Buchi" in nba.to_hoa()
    npa = NPA(AB, 2, 0, [(0, "a", 1, 0), (0, "b", 0, 1), (1, "b", 0, 1)])
    assert "acc-name: parity min even" in npa.to_hoa()
    assert verdicts(PropNPA.from_hoa(PropNPA.from_hoa(NPA_TEXT).to_hoa())) == verdicts(PropNPA.from_hoa(NPA_TEXT))


def test_only_classes_that_the_crate_can_write_have_to_hoa():
    for cls in (DBA, DPA, NBA, NPA, PropDBA, PropDPA, PropNBA, PropNPA):
        assert hasattr(cls, "to_hoa"), cls
    for cls in (DCA, NCA, PropDCA, PropNCA):
        assert hasattr(cls, "to_hoa"), cls
    for cls in (DFA, NFA, MooreMachine, MealyMachine, PropDFA):
        assert not hasattr(cls, "to_hoa"), cls
    for cls in (PropDBA, PropDCA, PropDPA, PropNBA, PropNCA, PropNPA):
        assert hasattr(cls, "from_hoa"), cls
    # the classes over a CharAlphabet cannot be read, HOA automata have propositions
    for cls in (DBA, DPA, NBA, NPA, DCA, NCA, DFA, NFA, PropDFA):
        assert not hasattr(cls, "from_hoa"), cls


def test_conversions_keep_the_language():
    dca = PropDCA(P, 1, 0, [(0, T, True, 0), (0, F, False, 0)])
    dba_ = PropDBA.from_hoa(DBA_TEXT)
    dpa_from_dba = PropDPA.from_dba(dba_)
    assert verdicts(dpa_from_dba) == verdicts(dba_)
    assert (dpa_from_dba.num_states, dpa_from_dba.num_edges) == (1, 2)
    assert verdicts(PropDPA.from_dca(dca)) == verdicts(dca)
    assert verdicts(PropNCA.from_dca(dca)) == verdicts(dca)
    dpa = PropDPA.from_hoa(DPA_TEXT)
    assert verdicts(PropNPA.from_dpa(dpa)) == verdicts(dpa)
    assert PropNPA.from_dpa(dpa).num_edges == dpa.num_edges


def test_conversions_of_character_automata():
    dba_ = DBA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)])
    dpa = DPA.from_dba(dba_)
    for w in [OmegaWord("", "a"), OmegaWord("a", "b"), OmegaWord("", "ab")]:
        assert dpa.accepts(w) == dba_.accepts(w)
    dca = DCA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)])
    assert DPA.from_dca(dca).accepts(OmegaWord("aa", "b"))
    assert not DPA.from_dca(dca).accepts(OmegaWord("", "ab"))
    assert NCA.from_dca(dca).accepts(OmegaWord("aa", "b"))
    assert not NCA.from_dca(dca).accepts(OmegaWord("", "ab"))
    assert NPA.from_dpa(dpa).accepts(OmegaWord("b", "a")) == dpa.accepts(OmegaWord("b", "a"))


def test_to_dot():
    dfa = DFA(AB, 2, 0, [1], [(0, "a", 1), (0, "b", 0), (1, "a", 1), (1, "b", 0)])
    dot = dfa.to_dot()
    assert dot.startswith("digraph") and "doublecircle" in dot and dot.rstrip().endswith("}")
    for aut in (
        DBA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)]),
        DPA(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 0, 0)]),
        PropDBA.from_hoa(DBA_TEXT),
        PropDPA.from_hoa(DPA_TEXT),
        MooreMachine(AB, [0, 1], 0, [(0, "a", 1), (0, "b", 0), (1, "a", 1), (1, "b", 0)]),
        MealyMachine(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 0, 0)]),
        PropDFA(P, 1, 0, [0], [(0, T, 0), (0, F, 0)]),
    ):
        assert aut.to_dot().startswith("digraph"), aut


def test_repr_svg_draws_an_svg_image():
    for aut in (
        DFA(AB, 1, 0, [0], [(0, "a", 0), (0, "b", 0)]),
        DBA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)]),
        PropDPA.from_hoa(DPA_TEXT),
        PropDBA.from_hoa(DBA_TEXT),
        MooreMachine(AB, [0], 0, [(0, "a", 0), (0, "b", 0)]),
        MealyMachine(AB, 1, 0, [(0, "a", 1, 0), (0, "b", 0, 0)]),
    ):
        svg = aut._repr_svg_()
        assert "<svg" in svg and svg.rstrip().endswith("</svg>"), aut


def test_classes_without_a_dot_style_in_the_crate_have_no_dot_output():
    for cls in (DCA, NBA, NCA, NPA, NFA, PropNBA):
        assert not hasattr(cls, "to_dot") and not hasattr(cls, "_repr_svg_"), cls


def test_module_exports():
    assert callable(automata.parse_hoa) and callable(automata.parse_hoa_all)
    assert issubclass(HoaError, automata.Error)


def test_co_buchi_round_trips_and_parse_hoa_returns_it():
    dca = PropDCA(P, 1, 0, [(0, T, True, 0), (0, F, False, 0)])
    text = dca.to_hoa()
    assert "acc-name: co-Buchi" in text
    assert verdicts(PropDCA.from_hoa(text)) == verdicts(dca) == [False, True, False, True, False]
    assert type(parse_hoa(text)) is PropDCA
    # characters become propositions
    assert "acc-name: co-Buchi" in DCA(AB, 1, 0, [(0, "a", True, 0), (0, "b", False, 0)]).to_hoa()
    # the nondeterministic class reads deterministic text too
    assert verdicts(PropNCA.from_hoa(text)) == verdicts(dca)

    nca = PropNCA(P, 2, 0, [(0, T, True, 0), (0, F, True, 0), (0, F, False, 1), (1, F, False, 1)])
    nca_text = nca.to_hoa()
    assert "acc-name: co-Buchi" in nca_text and "acc-name: co-Buchi" in NCA(AB, 1, 0, [(0, "a", True, 0)]).to_hoa()
    assert verdicts(PropNCA.from_hoa(nca_text)) == verdicts(nca) == [False, True, False, True, False]
    assert type(parse_hoa(nca_text)) is PropNCA
    assert [type(a) for a in parse_hoa_all(text + nca_text)] == [PropDCA, PropNCA]
    with pytest.raises(HoaError, match="not deterministic"):
        PropDCA.from_hoa(nca_text)


def test_co_buchi_is_not_confused_with_buchi():
    dca_text = PropDCA(P, 1, 0, [(0, T, True, 0), (0, F, False, 0)]).to_hoa()
    with pytest.raises(HoaError, match="Büchi"):
        PropDBA.from_hoa(dca_text)
    with pytest.raises(HoaError, match="co-Büchi"):
        PropDCA.from_hoa(DBA_TEXT)
    with pytest.raises(HoaError, match="co-Büchi"):
        PropNCA.from_hoa(NBA_TEXT)
    with pytest.raises(HoaError):
        PropNBA.from_hoa(dca_text)
    # a DPA reads it as `from_dca` does
    assert verdicts(PropDPA.from_hoa(dca_text)) == verdicts(PropDCA.from_hoa(dca_text))
    with pytest.raises(HoaError):
        PropDCA.from_hoa("garbage")
