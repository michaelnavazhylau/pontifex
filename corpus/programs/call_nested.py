"""Helper calls inside expressions, arguments, arrays, and a loop."""

def scale(x, factor):
    return x * factor


def advance(x, v, dt, n):
    v = scale(v, dt) + scale(n, 1)
    xs = [x, v]
    xs[0] = scale(xs[1], 2) + xs[0]
    while n > 0:
        v = scale(v, 1) + scale(n, 1)
        n = n - 1
    return xs[0], v
