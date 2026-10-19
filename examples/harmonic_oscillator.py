"""Harmonic oscillator x'' = -omega^2 x, one velocity-first Euler step.

`omega2` is omega squared (so the update stays multiplication-only, which keeps
the exact-rational algebra in scope).
"""


def step(x: float, v: float, omega2: float, dt: float) -> tuple[float, float]:
    v = v - omega2 * x * dt
    x = x + v * dt
    return x, v
