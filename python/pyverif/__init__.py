"""pyverif: a Python -> SSA IR -> Lean 4 verification pipeline.

Public surface:

* :func:`pyverif.frontend.translate` -- restricted Python subset to SSA IR
* :func:`pyverif.emit.emit_module` -- IR to Lean 4 source
* :func:`pyverif.interp.run_exact` / ``run_float`` -- reference semantics
* :func:`pyverif.pipeline.compile_source` -- the whole pipeline
"""

from .errors import FrontendError, InterpreterError, PyVerifError, UnsupportedError
from .frontend import Translated, translate
from .interp import FellThrough, OutOfFuel, Returned, run_exact, run_float
from .pipeline import Artifacts, compile_file, compile_source

__all__ = [
    "Artifacts",
    "FellThrough",
    "FrontendError",
    "InterpreterError",
    "OutOfFuel",
    "PyVerifError",
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
