# White-box calls (T13, first slice)

Select an entry point explicitly when a module has multiple functions:

```bash
uv run python -m pontifex emit examples/call_step.py --function advance --out /tmp/CallStep.lean
lake env lean /tmp/CallStep.lean
```

```python
def velocity(v, a, dt):
    delta = a * dt
    v += delta
    return v


def advance(x, v, a, dt):
    v = velocity(v, a, dt)
    x += v * dt
    return x, v
```

## Supported boundary

* A call is the **whole value** of `name = helper(...)`, `name: T = helper(...)`,
  or `return helper(...)`. Assignment callees return one scalar. A caller may
  still return multiple scalars normally, but all its returns must agree in arity.
* Helpers are module-local functions with straight-line assignments, `pass`/
  docstrings, and one final scalar return. Existing signature restrictions apply;
  annotations remain advisory. Parameters may be reassigned.
* Arguments are positional scalar expressions. Caller array reads and lengths
  are scalar arguments; arrays themselves cannot cross the call boundary.
* Forward references and acyclic chains of supported helper calls work. Each
  helper is independently lowered and its direct dependencies are recorded.
* Callers retain their existing branches, loops, early returns, and local arrays.
  Callee locals do not leak into the caller's merges or loop-carried variables.
* A local binding shadows a function/builtin throughout its Python scope, even
  before the assignment. Such calls are rejected rather than treated as globals.
  Duplicate module function definitions are also rejected.

Scalar `min`/`max` and conditional expressions are supported inside straight-line
helpers and scalar call arguments; see [SELECTION.md](SELECTION.md).

Deferred: user-helper calls inside arithmetic/conditions/arguments, keyword/starred calls,
ignored-result calls, tuple unpacking/results, callee branches/loops/early
returns, array arguments/results/locals in helpers, recursion, external calls,
and summary/opaque calls. Unsupported shapes fail with located diagnostics.

## Expansion and certificates

Calls add **no runtime call node or JSON schema change**: they landed on schema
3; the current schema is 4 after T15a's scalar-selection extension. At each call site Python's inliner:

1. allocates fresh slots for the whole callee frame;
2. evaluates arguments once, left to right, into the parameter slots;
3. relocates the callee's assignments into that frame;
4. assigns the final scalar to a fresh caller result slot, or retains `ret`
   for a tail call.

Unused arguments and dead-but-eager callee computations are not removed.
Failures propagate in Python evaluation order; no call is hoisted out of its
branch or loop. Fuel measures the **expanded IR's structured depth**, not Python
call depth, and expansion can increase the needed budget.

The emitted core Source AST retains an `inlineCall` referencing the independently
emitted callee IR (inside a private `CalleeN` namespace). `Source.lowerBody`
expands it with Lean's independent `Inline.expand` algorithm. The caller's usual
`<fn>_lowering := rfl` checks argument transcription, frame offsets, expansion,
and the surrounding SSA lowering. The callee's own `_lowering := rfl` checks
its source-to-IR agreement.

**`<fn>_program_lowering`** composes the caller's lowering fact with every
callee's program certificate recursively. For calls, this is the complete
lowering evidence: the caller's `_lowering` alone checks expansion of the
referenced IR, not that callee IR's agreement with its source. All generated
per-function/program lowering and code-linkage certificates are axiom-audited.
The existing `_link` / `_compiled_link` then check the independently emitted
executable against the expanded IR; no codegen/interpreter changes are needed.

As before, these are per-program agreement checks, **not a semantic-preservation
proof of Python desugaring or inlining**. The inliner's fidelity and the Python
AST transcription remain tested trust boundaries. Regression tests include
kernel rejection of corrupted callee source, caller IR, arguments, and frame
sizes. See [TRUST.md](TRUST.md).
