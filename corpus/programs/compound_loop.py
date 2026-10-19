def balance(n, principal, rate):
    i = 0
    while i < n:
        principal = principal * (1 + rate)
        i = i + 1
    return principal
