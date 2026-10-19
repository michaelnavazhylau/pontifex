def step(x, y):
    result = x
    if y != 0 and x / y > 1:
        result = x / y
    return result
