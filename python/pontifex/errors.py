"""Frontend errors.

Every rejection carries a source location.  The frontend is intentionally
strict: anything outside the documented subset is rejected here rather than
being silently given an unintended semantics.
"""

from __future__ import annotations

import ast


class PontifexError(Exception):
    """Base class for user-facing errors."""


class FrontendError(PontifexError):
    """The source program is outside the supported Python subset."""

    def __init__(self, message: str, node: ast.AST | None = None, filename: str = "<unknown>"):
        self.message = message
        self.filename = filename
        self.lineno = getattr(node, "lineno", None)
        self.col_offset = getattr(node, "col_offset", None)
        location = filename
        if self.lineno is not None:
            location += f":{self.lineno}"
            if self.col_offset is not None:
                location += f":{self.col_offset + 1}"
        super().__init__(f"{location}: {message}")

    def describe(self, source: str | None = None) -> str:
        text = str(self)
        if source is not None and self.lineno is not None:
            lines = source.splitlines()
            if 0 <= self.lineno - 1 < len(lines):
                text += "\n  " + lines[self.lineno - 1].rstrip()
        return text


class UnsupportedError(FrontendError):
    """A specific construct is not in the verified subset."""


class InterpreterError(PontifexError):
    """The reference interpreter hit an undefined operation (e.g. 0 division)."""
