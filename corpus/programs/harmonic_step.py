def step(x, v, omega2, dt):
    v = v - omega2 * x * dt
    x = x + v * dt
    return x, v
