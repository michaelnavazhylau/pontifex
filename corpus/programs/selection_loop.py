"""Scalar selection in loop bodies, guards, and early returns."""


def advance(x, n):
    while n > 0:
        x = min(x + 1, 8) if x > 0 else max(x + 2, -8)
        if (x if n > 1 else 0) > 5:
            return min(x, 5)
        n -= 1
    return x
