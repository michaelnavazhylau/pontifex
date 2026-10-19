def partial_sum(n, term, ratio):
    total = 0
    i = 0
    while i < n:
        total = total + term
        term = term * ratio
        i = i + 1
    return total, term
