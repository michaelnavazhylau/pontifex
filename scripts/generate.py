#!/usr/bin/env python3
"""Regenerate the checked-in Lean translations of ``examples/*.py``.

    python scripts/generate.py            # write certificates + NativeTests.lean
    python scripts/generate.py --check    # fail if the files are stale

Every generated module contains:

* ``<fn>IR``            -- the SSA IR as a Lean value,
* ``<fn>``              -- the functional translation,
* ``<fn>Source``        -- the core source AST emitted by the frontend,
* ``<fn>_lowering``     -- `rfl` certificate that the verified lowering
                           reproduces ``<fn>IR.body``,
* ``<fn>_link``        -- kernel linkage (rfl for straight-line programs),
* ``<fn>_compiled_link`` -- all-fuel, all-backend linkage for control flow,
Finite native sample checks live only in ``NativeTests.lean``, built with the
explicit ``lake build PontifexNativeTests`` target, never imported by certificates.

The same IR is written to ``build/ir/<stem>.json`` for the Lean JSON consumer
and for differential testing.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))

from pontifex.emit import emit_native_samples, needs_checked_backend
from pontifex.frontend import translate
from pontifex.pipeline import compile_source, conformance_pairs, default_namespace
from pontifex.version import IR_VERSION

EXAMPLES = [
    "free_fall",
    "harmonic_oscillator",
    "free_fall_loop",
    "clamped_step",
    "early_exit",
    "array_step",
    "call_step",
    "limited_step",
    "call_nested",
]

# Multi-function modules must select the public entry point explicitly.
EXAMPLE_FUNCTIONS = {"call_step": "advance", "call_nested": "advance"}

FUEL = 64


def check_schema_alignment(config_path: Path | None = None, expected: int | None = None) -> None:
    """Fail early when the Python and Lean schema versions diverge."""
    config_path = config_path or (ROOT / "Pontifex" / "Core" / "Config.lean")
    expected = IR_VERSION if expected is None else expected
    config = config_path.read_text()
    marker = "def irSchemaVersion : Nat :="
    if marker not in config:
        raise SystemExit(f"cannot find {marker!r} in {config_path}")
    tail = config.split(marker, 1)[1].strip()
    lean_version = int(tail.split()[0])
    if lean_version != expected:
        raise SystemExit(
            f"schema version mismatch: python/pontifex/version.py has IR_VERSION={expected}, "
            f"{config_path} has irSchemaVersion={lean_version}"
        )


def generate_one(stem: str) -> tuple[str, str, str]:
    namespace = default_namespace(stem)
    # Relative paths keep generated headers deterministic across checkouts.
    path = ROOT / "examples" / f"{stem}.py"
    artifacts = compile_source(
        path.read_text(),
        filename=str(path.relative_to(ROOT)),
        function=EXAMPLE_FUNCTIONS.get(stem),
        namespace=namespace,
        fuel=FUEL,
        generator="python scripts/generate.py",
    )
    samples = emit_native_samples(
        artifacts.fn,
        namespace=namespace,
        fuel=FUEL,
        conformance=conformance_pairs(artifacts, fuel=FUEL),
    )
    return artifacts.lean_source, artifacts.ir_json, samples


AUDIT_EXAMPLES = [
    "Pontifex.Examples.freeFall_matches_spec",
    "Pontifex.Examples.harmonicOscillator_matches_spec",
    "Pontifex.Examples.freeFall_ir_matches_spec",
    "Pontifex.Examples.clampedStep_matches_spec",
    "Pontifex.Examples.freeFallLoop_float_link",
    "Pontifex.Examples.freeFallLoop_zero_budget",
    "Pontifex.Binary64.bits_roundtrip",
    "Pontifex.exec_mono",
    "Pontifex.exec_completed_stable",
    "Pontifex.total_to_partial",
    "Pontifex.Outcome.refines_trans",
    "Pontifex.Outcome.refines_antisymm",
    "Pontifex.Examples.rat_div_success_iff",
    "Pontifex.Examples.rat_div_failed_iff",
    "Pontifex.Examples.freeFallLoop_compiled_mono",
    "Pontifex.Examples.freeFallLoop_zero_time_total",
    "Pontifex.Examples.freeFallLoop_zero_time_partial",
    "Pontifex.Spec.symplecticStep_modifiedEnergy",
    "Pontifex.Spec.modifiedEnergyGridOk_eq_true",
    "Pontifex.Spec.repeatStep_velocity",
    "Pontifex.Spec.repeatStep_position_twice",
    "Pontifex.Spec.ratNatCast_add",
    "Pontifex.Spec.ratNatCast_mul",
    "Pontifex.Spec.ratNatCast_succ",
    "Pontifex.Poly.eval_normalize",
    "Pontifex.Poly.eval_insertTerm",
    "Pontifex.Poly.eval_foldr_mul",
    "Pontifex.Examples.freeFall_step_position",
    "Pontifex.Examples.freeFall_step_velocity",
    "Pontifex.Examples.harmonicOscillator_step_velocity",
    "Pontifex.FloatSpec.add_value",
    "Pontifex.FloatSpec.add_bits",
    "Pontifex.FloatSpec.mul_value",
    "Pontifex.FloatSpec.div_value",
    "Pontifex.FloatSpec.sub_bits",
    "Pontifex.Binary64.neg_bits",
    "Pontifex.Binary64.abs_bits",
]


def audit_content() -> str:
    """All kernel-checked certificates, audited for disallowed axioms."""
    names: list[str] = []

    def add_certificates(translated, namespace: str) -> None:
        for index, callee in enumerate(translated.callees):
            add_certificates(callee, f"{namespace}.Callee{index}")
        fn = translated.fn
        names.append(f"{namespace}.{fn.name}_lowering")
        names.append(f"{namespace}.{fn.name}_program_lowering")
        if needs_checked_backend(fn.body):
            names.append(f"{namespace}.{fn.name}_compiled_link")
        names.append(f"{namespace}.{fn.name}_link")

    for stem in EXAMPLES:
        path = ROOT / "examples" / f"{stem}.py"
        translated = translate(
            path.read_text(),
            filename=str(path.relative_to(ROOT)),
            function=EXAMPLE_FUNCTIONS.get(stem),
        )
        add_certificates(translated, default_namespace(stem))
    names.extend(AUDIT_EXAMPLES)
    lines = [
        "/- Generated by scripts/generate.py: kernel axiom audit of every certificate.",
        "   DO NOT EDIT. `#audit_axioms` rejects sorryAx, native_decide trust hooks,",
        "   and project-specific axioms. -/",
        "import Pontifex.Generated",
        "import Pontifex.Examples.SpecLinks",
        "import Pontifex.Examples.ControlFlow",
        "import Pontifex.Examples.FailuresAndRefinement",
        "import Pontifex.Audit.Command",
        "",
    ]
    lines.extend(f"#audit_axioms {name}" for name in names)
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="verify files are up to date")
    args = parser.parse_args(argv)
    check_schema_alignment()

    stale: list[str] = []
    native_samples = [
        "/- Generated by scripts/generate.py. DO NOT EDIT.",
        "   Finite native conformance tests ONLY, not correctness certificates.",
        "   Explicit test target: lake build PontifexNativeTests. -/",
        "import Pontifex.Generated\n",
    ]
    for stem in EXAMPLES:
        lean, ir_json, samples = generate_one(stem)
        native_samples.append(samples)
        namespace = default_namespace(stem)
        lean_path = ROOT / "Pontifex" / "Generated" / f"{namespace.split('.')[-1]}.lean"
        ir_path = ROOT / "build" / "ir" / f"{stem}.json"
        if args.check:
            if not lean_path.exists() or lean_path.read_text() != lean:
                stale.append(str(lean_path))
            # ``build/ir`` is gitignored: a fresh checkout has no cache to compare.
            if ir_path.exists() and ir_path.read_text() != ir_json:
                stale.append(str(ir_path))
            continue
        lean_path.parent.mkdir(parents=True, exist_ok=True)
        ir_path.parent.mkdir(parents=True, exist_ok=True)
        lean_path.write_text(lean)
        ir_path.write_text(ir_json)
        print(f"wrote {lean_path.relative_to(ROOT)} and {ir_path.relative_to(ROOT)}")

    native_path = ROOT / "NativeTests.lean"
    native_content = "\n".join(native_samples)
    if args.check:
        if not native_path.exists() or native_path.read_text() != native_content:
            stale.append(str(native_path))
    else:
        native_path.write_text(native_content)
        print(f"wrote {native_path.relative_to(ROOT)}")

    audit_path = ROOT / "Pontifex" / "Audit.lean"
    audit = audit_content()
    if args.check:
        if not audit_path.exists() or audit_path.read_text() != audit:
            stale.append(str(audit_path))
    else:
        audit_path.write_text(audit)
        print(f"wrote {audit_path.relative_to(ROOT)}")

    umbrella = ROOT / "Pontifex" / "Generated.lean"
    imports = "\n".join(
        f"import Pontifex.Generated.{default_namespace(stem).split('.')[-1]}" for stem in EXAMPLES
    )
    content = (
        "/- Umbrella module for the checked-in generated translations.\n"
        "   Regenerate with `python scripts/generate.py`. -/\n" + imports + "\n"
    )
    if args.check:
        if not umbrella.exists() or umbrella.read_text() != content:
            stale.append(str(umbrella))
    else:
        umbrella.write_text(content)
        print(f"wrote {umbrella.relative_to(ROOT)}")

    if args.check and stale:
        print("stale generated artifacts:", *stale, sep="\n  ")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
