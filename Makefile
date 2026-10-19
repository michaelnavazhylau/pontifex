# pontifex — Python -> SSA IR -> Lean 4 verification bridge

PY ?= python3
LAKE ?= lake

.PHONY: all lean gen test check clean fmt fmt-check corpus rejections float-boundaries

all: lean test

## Lean: library, generated examples, and the conformance runner
lean:
	$(LAKE) build

## Regenerate the checked-in translations of examples/
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
check: fmt-check gen
	$(PY) scripts/generate.py --check
	$(PY) scripts/update_rejections.py --check
	$(LAKE) build
	$(PY) scripts/run_corpus.py --samples 8
	uv run python scripts/check_float_boundaries.py
	uv run pytest

test:
	uv run pytest

fmt-check:
	uv run ruff format --check python scripts

fmt:
	uv run ruff format python scripts
	uv run ruff check --fix python scripts 2>/dev/null || true

clean:
	rm -rf .lake/build build/ir/*.json .pytest_cache python/.pytest_cache
	find python -name __pycache__ -type d -prune -exec rm -rf {} +
