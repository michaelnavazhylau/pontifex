def step(x, v, a, dt):
    v = v + a * dt
    x = x + v * dt
    return x, v
