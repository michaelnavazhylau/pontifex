def simulate(t_end, x, v, a, dt):
    t = 0
    while t < t_end:
        v = v + a * dt
        x = x + v * dt
        t = t + dt
    return x, v
