"""Free fall integrated by a while loop until t >= t_end."""

def simulate(t_end: float, x: float, v: float, a: float, dt: float) -> tuple[float, float]:
    t = 0
    while t < t_end:
        v = v + a * dt
        x = x + v * dt
        t = t + dt
    return x, v
