def step(x, v, a, dt, limit):
    v = v + a * dt
    x = x + v * dt
    if x > limit:
        x = limit
        v = 0
    return x, v
