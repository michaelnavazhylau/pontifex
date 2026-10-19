"""Calls inside branches and a loop; tail calls on an early-exit path."""


def add_step(x, step):
    temp = x + step
    return temp


def advance(x, n):
    while n > 0:
        if x < 0:
            x = add_step(x, 2)
        else:
            x = add_step(x, 1)
        if x > 8:
            return add_step(x, -1)
        n -= 1
    return x
