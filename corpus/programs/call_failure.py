"""Both argument faults and dead-but-eager computations inside a callee."""


def helper(value, divisor):
    unused = 1 / divisor
    return value


def advance(x, y):
    return helper(x / y, x)
