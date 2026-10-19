"""pontifex: a Python -> SSA IR -> Lean 4 verification pipeline.

Public surface:

* :func:`pontifex.frontend.translate` -- restricted Python subset to SSA IR
* :func:`pontifex.emit.emit_module` -- IR to Lean 4 source
* :func:`pontifex.interp.run_exact` / ``run_float`` -- reference semantics
* :func:`pontifex.pipeline.compile_source` -- the whole pipeline
"""

from .errors import FrontendError, InterpreterError, PontifexError, UnsupportedError
from .frontend import Translated, translate
from .interp import FellThrough, OutOfFuel, Returned, Failed, Stuck, run_exact, run_float
from .pipeline import Artifacts, compile_file, compile_source

__all__ = [
    "Artifacts",
    "FellThrough",
    "Failed",
    "Stuck",
    "FrontendError",
    "InterpreterError",
    "OutOfFuel",
    "PontifexError",
    "Returned",
    "Translated",
    "UnsupportedError",
    "compile_file",
    "compile_source",
    "run_exact",
    "run_float",
    "translate",
]

__version__ = "0.1.0"
