"""A selected caller with a white-box scalar helper (T13's first slice)."""


def velocity(v, a, dt):
    delta = a * dt
    v += delta
    return v


def advance(x, v, a, dt):
    v = velocity(v, a, dt)
    x += v * dt
    return x, v
