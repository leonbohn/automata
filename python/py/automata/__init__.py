"""Transition systems and automata over finite and infinite words."""

from automata import _automata
from automata._automata import *  # noqa: F403  (every class and exception of the extension)
from automata._automata import __version__
from automata.builders import __all__ as _builders
from automata.builders import *  # noqa: F403

# `Error` is the documented base class; `AutomataError` is its name on the Rust side
Error = _automata.AutomataError  # noqa: F405

__all__ = sorted({n for n in dir(_automata) if not n.startswith("_")} | {"Error", "__version__", *_builders})
