def integrate(dt: float, n: float):
    xs = [0.0, 0.0, 0.0]
    i = 0
    while i < n:
        xs[i] = xs[i] + dt
        i = i + 1
    return xs[0], xs[1], xs[2], len(xs)
