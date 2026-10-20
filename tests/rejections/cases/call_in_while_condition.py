def helper(x):
    return x + 1


def f(x):
    while helper(x) > 0:
        x = x - 1
    return x
