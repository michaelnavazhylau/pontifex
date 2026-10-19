"""Saturating integrator with guard-clause and loop early exits."""

def advance(x: float, v: float, n: float):
    if n <= 0:
        return x, v
    while n > 0:
        if x > 8:
            return 8, v
        v = v + 1
        x = x + v
        n = n - 1
    return x, v
