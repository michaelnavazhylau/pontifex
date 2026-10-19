"""Finite clamp with stable two-argument min/max semantics."""


def advance(x, v, a, dt, limit):
    v = min(max(v + a * dt, -limit), limit)
    x += v * dt
    return x if x > 0 else 0, v
