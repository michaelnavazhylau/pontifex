def accumulate(n, m, step):
    acc = 0
    i = 0
    j = 0
    while i < n:
        j = 0
        while j < m:
            acc = acc + i * j * step
            j = j + 1
        i = i + 1
    return acc
