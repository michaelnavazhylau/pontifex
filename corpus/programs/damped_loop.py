def simulate(t_end, x, v, omega2, dt):
    t = 0
    while t < t_end:
        v = v - omega2 * x * dt
        x = x + v * dt
        t = t + dt
    return x, v
