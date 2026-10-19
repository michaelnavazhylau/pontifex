def step(x, v, dt, limit):
    x = x + v * dt
    if x > limit:
        x = limit
        v = 0
    return x, v
