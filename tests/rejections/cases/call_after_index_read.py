def helper(x):
    return x + 1


def f(x):
    xs = [x]
    return xs[0] + helper(x)
