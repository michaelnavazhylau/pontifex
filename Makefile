# pyverif — Python -> SSA IR -> Lean 4 verification bridge

PY ?= python3
LAKE ?= lake

.PHONY: all lean gen test check clean fmt

all: lean test

## Lean: library, generated examples, and the conformance runner
lean:
	$(LAKE) build

## Regenerate the checked-in translations of examples/
gen:
	$(PY) scripts/generate.py

## CI-style: generated artifacts fresh + Python tests + Lean build
check: gen
	$(PY) scripts/generate.py --check
	$(LAKE) build
	uv run pytest

test:
	uv run pytest

fmt:
	ruff format python 2>/dev/null || true
	ruff check --fix python 2>/dev/null || true

clean:
	rm -rf .lake/build build/ir/*.json .pytest_cache python/.pytest_cache
	find python -name __pycache__ -type d -prune -exec rm -rf {} +
