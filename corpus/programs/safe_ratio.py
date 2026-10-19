"""The unselected conditional branch must not divide by zero."""


def ratio(x, y):
    value = x / y if y != 0 else 0
    return min(max(value, -8), 8)
