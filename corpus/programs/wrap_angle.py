def wrap(theta, period):
    while theta > period:
        theta = theta - period
    while theta < 0:
        theta = theta + period
    return theta
