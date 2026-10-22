# pontifex — Python -> SSA IR -> Lean 4 verification bridge

PY ?= python3
LAKE ?= lake

.PHONY: all lean gen test check clean fmt fmt-check lint corpus rejections float-boundaries native-tests workflow-plan workflow-check

all: lean test

## Lean: library, generated examples, and the conformance runner
lean:
	$(LAKE) build

## Explicit native sample tests (not correctness certificates / default build)
native-tests:
	$(LAKE) build PontifexNativeTests

## Regenerate the checked-in translations of examples/ and native tests
gen:
	$(PY) scripts/generate.py

## Bit-exact Float boundary corpus (100,000 random patterns + IEEE edge cases)
float-boundaries: lean
	uv run python scripts/check_float_boundaries.py

## Differential corpus (requires `lake build pontifex`)
corpus:
	$(PY) scripts/run_corpus.py --samples 32

## Regenerate expected rejection diagnostics after reviewing a change
rejections:
	$(PY) scripts/update_rejections.py

## CI-style: format + generated artifacts fresh + Python tests + Lean build + audit
check: fmt-check
	$(PY) scripts/generate.py --check
	$(PY) scripts/update_rejections.py --check
	$(LAKE) build
	$(LAKE) build PontifexNativeTests
	$(PY) scripts/run_corpus.py --samples 8
	uv run python scripts/check_float_boundaries.py
	uv run pytest

test:
	uv run pytest

fmt-check:
	uv run ruff format --check python scripts

fmt:
	uv run ruff format python scripts

## Lint is separate from formatting; failures are never suppressed.
lint:
	uv run ruff check python scripts

## Read-only source checks; use `make gen` explicitly when artifacts are stale.
workflow-plan:
	uv run --locked --no-sync python scripts/pontifex_workflow.py plan --profile focused

workflow-check:
	uv run --locked --no-sync python scripts/pontifex_workflow.py validate --profile full

clean:
	rm -rf .lake/build build/ir/*.json .pytest_cache python/.pytest_cache
	find python -name __pycache__ -type d -prune -exec rm -rf {} +
