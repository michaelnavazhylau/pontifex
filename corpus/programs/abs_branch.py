def step(x, y):
    if abs(x) > abs(y):
        x = x - y
    else:
        y = y - x
    return x, y
