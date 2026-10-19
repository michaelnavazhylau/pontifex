"""Transitive, positional scalar helpers with reassigned parameters."""


def delta(a, dt):
    return a * dt


def velocity(v, a, dt):
    dv = delta(a, dt)
    v += dv
    return v


def advance(x, v, a, dt):
    v = velocity(v, a, dt)
    x += v * dt
    return x, v
