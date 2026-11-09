"""Solving parity games (max-even), compared with Spot and Oink.

The games are written in the PGSolver format; each contender reads them itself before the timed
call. Oink runs as a process, we use the time it reports for preprocessing plus solving.
`zlk` is its Zielonka, `ppp` priority promotion (PP+), the solver Oink recommends.
"""

import os
import pathlib
import re
import shutil
import subprocess
import tempfile

import automata
import spot
from compare import Case, Contender, operation

# Spot has at most 32 acceptance sets, which limits the number of priorities to 30 here
SIZES = (10_000, 50_000)
OINK_SOLVERS = ("zlk", "ppp")


class Rng:
    """xorshift64, the generator of `benches/game.rs`: the games are the same everywhere."""

    def __init__(self):
        self.x = 0x9E3779B97F4A7C15

    def below(self, n):
        mask = (1 << 64) - 1
        self.x ^= (self.x << 13) & mask
        self.x ^= self.x >> 7
        self.x ^= (self.x << 17) & mask
        return self.x % n


def pgsolver(owners, priorities, successors):
    lines = [f"parity {len(owners) - 1};"]
    for v, (o, p, s) in enumerate(zip(owners, priorities, successors)):
        lines.append(f"{v} {p} {o} {','.join(map(str, s))};")
    return "\n".join(lines) + "\n"


def random_game(n, priorities):
    """`1..=3` successors per vertex, owners and priorities at random."""
    rng = Rng()
    owners = [rng.below(2) for _ in range(n)]
    prios = [rng.below(priorities) for _ in range(n)]
    succ = [[rng.below(n) for _ in range(1 + rng.below(3))] for _ in range(n)]
    return pgsolver(owners, prios, succ)


def ladder(n):
    """A ring of alternating owners and cycling priorities with an edge back to vertex 0."""
    return pgsolver(
        [i % 2 for i in range(n)],
        [i % 30 for i in range(n)],
        [sorted({(i + 1) % n, 0}) for i in range(n)],
    )


GAMES = {
    "random_few": lambda n: random_game(n, 4),
    "random_many": lambda n: random_game(n, 30),
    "ladder": ladder,
}


def oink_binary():
    return os.environ.get("OINK") or shutil.which("oink")


def run_oink(binary, solver, path, n):
    """Winners (True = Eve, Oink's player 0) and Oink's own solving time in seconds."""
    with tempfile.TemporaryDirectory() as tmp:
        sol = pathlib.Path(tmp) / "out.sol"
        proc = subprocess.run(
            [binary, "-w", "1", f"--{solver}", path, str(sol)],
            capture_output=True,
            text=True,
            check=True,
        )
        found = re.search(r"total solving time: ([0-9.eE+-]+) sec", proc.stdout)
        if found is None:
            raise RuntimeError(f"unexpected output of oink:\n{proc.stdout[-500:]}")
        seconds = float(found.group(1))
        eve = [False] * n
        for line in sol.read_text().splitlines()[1:]:
            fields = line.rstrip(";").split()
            eve[int(fields[0])] = fields[1] == "0"
        return eve, seconds


@operation("game/solve")
def solve(ctx):
    oink = oink_binary()
    ctx.settings["spot"] = spot.version()
    ctx.settings["oink"] = (
        {"binary": oink, "solvers": list(OINK_SOLVERS), "workers": 1} if oink else None
    )
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="versus-games-"))
    for kind, make in GAMES.items():
        for n in SIZES:
            text = make(n)
            path = tmp / f"{kind}_{n}.gm"
            path.write_text(text)
            game = automata.MaxEvenParityGame.from_pgsolver(text)
            s_game = spot.automaton(str(path))

            def ours(game=game):
                return [w == "eve" for w in game.solve()]

            def theirs(s_game=s_game):
                spot.solve_parity_game(s_game, True)  # globally: all vertices, not just the initial one
                return [not odd for odd in spot.get_state_winners(s_game)]  # True = player 1 = Adam

            refs = {"spot": Contender(theirs, lambda r: len(r))}
            if oink:
                for solver in OINK_SOLVERS:
                    refs[f"oink-{solver}"] = Contender(
                        lambda s=solver, p=str(path), n=n: run_oink(oink, s, p, n), len
                    )
            yield Case(f"{kind}_{n}", Contender(ours, len), refs)
