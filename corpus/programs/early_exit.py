def advance(x: float, n: float):
    if n <= 0:
        return x
    while n > 0:
        if x > 8:
            return 8
        x = x + 1
        n = n - 1
    return x
