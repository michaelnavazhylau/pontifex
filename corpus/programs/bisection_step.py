def step(a, b, fa, fb):
    mid = (a + b) / 2
    if fa * fb <= 0:
        a = mid
    else:
        b = mid
    return a, b
