def step(state, rate, cap):
    if state < 0:
        state = 0
    next_state = state * (1 + rate)
    if next_state > cap:
        next_state = cap
    return next_state, state
