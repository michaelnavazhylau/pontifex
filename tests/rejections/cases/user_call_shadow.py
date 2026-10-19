def helper(x):
    return x


def f(x):
    y = helper(x)
    helper = x
    return y
