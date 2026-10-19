def step(x, v, a, dt):
    x = x + v * dt + a * dt * dt
    v = v + 2 * a * dt
    return x, v
