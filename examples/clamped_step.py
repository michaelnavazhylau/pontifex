"""One step with a position clamp: exercises branch merges (phi nodes)."""

def step(x: float, v: float, dt: float, limit: float) -> tuple[float, float]:
    x = x + v * dt
    if x > limit:
        x = limit
        v = 0
    return x, v
