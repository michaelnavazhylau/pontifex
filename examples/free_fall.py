"""Free fall: velocity-first (symplectic) Euler, one step.

The parameters are scalars; `dt` is the time step, `a` the constant
acceleration.  Returned values are the new position and velocity.
"""


def step(x: float, v: float, a: float, dt: float) -> tuple[float, float]:
    v = v + a * dt
    x = x + v * dt
    return x, v
