"""Command line interface.

python -m pontifex ir       FILE [--function F]       # SSA IR as JSON
python -m pontifex emit     FILE [--out PATH]         # Lean module
python -m pontifex compile  FILE --out PATH [--json PATH] [--with-samples]
python -m pontifex eval     FILE --args "1,2,3,4" [--float]
python -m pontifex doctor                              # toolchain discovery
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path

from .emit import emit_native_samples
from .errors import PontifexError
from .pipeline import (
    compile_file,
    conformance_pairs,
    default_namespace,
    find_lean_exe,
    run_exact,
    run_float,
    to_option,
)


def _parse_args_list(text: str, *, float_mode: bool = False) -> list:
    values = []
    for chunk in text.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        if not float_mode:
            values.append(Fraction(chunk))
        elif chunk.startswith("0x"):
            from .pipeline import _bits_to_float

            values.append(_bits_to_float(chunk))
        elif "/" in chunk:
            values.append(float(Fraction(chunk)))
        else:
            values.append(float(chunk))
    return values


def _compiled(args: argparse.Namespace):
    return compile_file(
        args.file,
        function=getattr(args, "function", None),
        namespace=getattr(args, "namespace", None),
        fuel=getattr(args, "fuel", 64),
    )


def cmd_ir(args: argparse.Namespace) -> int:
    print(_compiled(args).ir_json, end="")
    return 0


def cmd_emit(args: argparse.Namespace) -> int:
    artifacts = _compiled(args)
    if args.out:
        Path(args.out).write_text(artifacts.lean_source)
        print(f"wrote {args.out}")
    else:
        print(artifacts.lean_source, end="")
    return 0


def cmd_compile(args: argparse.Namespace) -> int:
    artifacts = _compiled(args)
    namespace = args.namespace or default_namespace(Path(args.file).stem)
    output = Path(args.out)
    output.write_text(artifacts.lean_source)
    written = [str(output)]
    if args.with_samples:
        # Standalone test input: embedding the same certificate avoids assuming
        # a Lake module path for arbitrary --out paths (including /tmp).
        samples = emit_native_samples(
            artifacts.fn,
            namespace=namespace,
            fuel=args.fuel,
            conformance=conformance_pairs(artifacts, fuel=args.fuel),
        )
        sample_path = output.with_name(f"{output.stem}.samples.lean")
        sample_path.write_text(artifacts.lean_source + samples)
        written.append(str(sample_path))
    if args.json:
        Path(args.json).write_text(artifacts.ir_json)
        written.append(str(args.json))
    print("wrote " + " and ".join(written))
    return 0


def cmd_eval(args: argparse.Namespace) -> int:
    artifacts = _compiled(args)
    values = _parse_args_list(args.args, float_mode=args.float)
    run = run_float if args.float else run_exact
    out = run(artifacts.fn, values, fuel=args.fuel)
    result = to_option(out)
    if result is None:
        from .interp import Failed

        print(f"Failed({out.error})" if isinstance(out, Failed) else type(out).__name__)
        return 1
    print(", ".join(str(v) for v in result))
    return 0


def cmd_doctor(args: argparse.Namespace) -> int:
    exe = find_lean_exe(Path.cwd())
    print(f"lean runner: {exe if exe else 'not built (run `lake build pontifex`)'}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="pontifex", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    def source_options(p: argparse.ArgumentParser) -> None:
        p.add_argument("file", help="Python source module (select an entry point with --function)")
        p.add_argument("--function", default=None, help="function to translate")
        p.add_argument("--namespace", default=None, help="Lean namespace")
        p.add_argument("--fuel", type=int, default=64, help="structured fuel for the expanded IR")

    p_ir = sub.add_parser("ir", help="print the SSA IR as JSON")
    source_options(p_ir)
    p_ir.set_defaults(func=cmd_ir)

    p_emit = sub.add_parser("emit", help="emit the Lean module")
    source_options(p_emit)
    p_emit.add_argument("--out", default=None, help="output .lean path")
    p_emit.set_defaults(func=cmd_emit)

    p_compile = sub.add_parser("compile", help="write Lean module and IR JSON")
    source_options(p_compile)
    p_compile.add_argument("--out", required=True, help="output .lean path")
    p_compile.add_argument("--json", default=None, help="output IR JSON path")
    p_compile.add_argument(
        "--with-samples",
        action="store_true",
        help="write a separate standalone <stem>.samples.lean native test module, not certificates",
    )
    p_compile.set_defaults(func=cmd_compile)

    p_eval = sub.add_parser("eval", help="evaluate the IR with the reference interpreter")
    source_options(p_eval)
    p_eval.add_argument("--args", required=True, help="comma separated exact rationals")
    p_eval.add_argument("--float", action="store_true", help="use binary64 arithmetic")
    p_eval.set_defaults(func=cmd_eval)

    p_doctor = sub.add_parser("doctor", help="report toolchain discovery")
    p_doctor.set_defaults(func=cmd_doctor)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except PontifexError as exc:
        print(f"pontifex: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
