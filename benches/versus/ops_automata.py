"""Operations on omega automata, compared with Spot (`import spot`).

Inputs are the DPAs of `benches/fixtures`. Spot reads the files itself; our side reads them with
`automata.parse_hoa`. The second automaton of a comparison is our `normalized()` variant of the
first (same language, other priorities), which both libraries read from HOA. (Spot's own
`postprocess` would be more interesting, but Spot permutes the atomic propositions of its HOA
output depending on what it has seen before, and `equivalent_to` rejects alphabets whose propositions are in another order.)
"""

import automata
import spot
from compare import Case, Contender, operation

def inputs(ctx):
    """`(name, spot automaton, our automaton, spot variant, our variant)` per fixture."""
    ctx.settings["spot"] = spot.version()
    for path in sorted((ctx.root / "benches" / "fixtures").glob("*/*.hoa")):
        name = f"{path.parent.name}/{path.stem}"
        s = spot.automaton(str(path))
        a = automata.parse_hoa(path.read_text())
        a_other = a.normalized()
        yield name, s, a, spot.automaton(a_other.to_hoa()), a_other


@operation("dpa/equivalence")
def equivalence(ctx):
    for name, s, a, s_other, a_other in inputs(ctx):
        yield Case(
            name,
            ours=Contender(lambda a=a, b=a_other: a.equivalent_to(b)),
            refs={"spot": Contender(lambda s=s, t=s_other: spot.are_equivalent(s, t))},
        )


@operation("dpa/inclusion")
def inclusion(ctx):
    for name, s, a, s_other, a_other in inputs(ctx):
        yield Case(
            name,
            ours=Contender(lambda a=a, b=a_other: a.included_in(b)),
            refs={"spot": Contender(lambda s=s, t=s_other: spot.contains(t, s))},
        )
