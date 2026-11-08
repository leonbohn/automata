"""Transition systems and automata over finite and infinite words."""

from automata._automata import (
    DFA,
    AcceptanceError,
    AutomataError,
    BuilderError,
    CharAlphabet,
    DFABuilder,
    HoaError,
    NotPeriodicError,
    PropAlphabet,
    PropAlphabetError,
    PropDFA,
    PropDFABuilder,
    __version__,
)

# `Error` is the documented base class; `AutomataError` is its name on the Rust side
Error = AutomataError

__all__ = [
    "DFA",
    "AcceptanceError",
    "AutomataError",
    "BuilderError",
    "CharAlphabet",
    "DFABuilder",
    "Error",
    "HoaError",
    "NotPeriodicError",
    "PropAlphabet",
    "PropAlphabetError",
    "PropDFA",
    "PropDFABuilder",
    "__version__",
]
