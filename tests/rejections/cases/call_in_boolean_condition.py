def helper(x):
    return x + 1


def f(x):
    if x > 0 and helper(x) != 0:
        return 1
    return 0
