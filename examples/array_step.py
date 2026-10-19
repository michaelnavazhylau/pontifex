"""A three-dimensional state vector advanced with a runtime index."""

def advance(i: float, dt: float):
    xs = [0.0, 0.0, 0.0]
    j = 0
    while j < len(xs):
        xs[j] = xs[j] + dt
        j = j + 1
    return xs[i], len(xs)
