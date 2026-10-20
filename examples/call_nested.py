"""A caller that uses a scalar helper inside expressions (T13 part 2)."""


def scale(x, factor):
    return x * factor


def advance(x, v, dt):
    v = scale(v, dt) + 1
    x += scale(v, dt)
    return x, v
