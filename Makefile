# pontifex — Python -> SSA IR -> Lean 4 verification bridge

PY ?= python3
LAKE ?= lake

.PHONY: all lean mathlib-spike gen test check clean fmt corpus rejections float-boundaries

all: lean test

## Lean: library, generated examples, and the conformance runner
lean:
	$(LAKE) build

## Optional Mathlib proof-power spike (not part of the default build)
mathlib-spike:
	$(LAKE) build MathlibSpike

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

## CI-style: generated artifacts fresh + Python tests + Lean build + audit
check: gen
	$(PY) scripts/generate.py --check
	$(PY) scripts/update_rejections.py --check
	$(LAKE) build
	$(PY) scripts/run_corpus.py --samples 8
	uv run python scripts/check_float_boundaries.py
	uv run pytest

test:
	uv run pytest

fmt:
	ruff format python 2>/dev/null || true
	ruff check --fix python 2>/dev/null || true

clean:
	rm -rf .lake/build build/ir/*.json .pytest_cache python/.pytest_cache
	find python -name __pycache__ -type d -prune -exec rm -rf {} +
