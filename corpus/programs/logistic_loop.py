def trajectory(n, x, r):
    i = 0
    while i < n:
        x = r * x * (1 - x)
        i = i + 1
    return x
