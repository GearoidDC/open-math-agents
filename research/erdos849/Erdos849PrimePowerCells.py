"""Integer height bounds for the simultaneous prime-power tuple theorem."""

from fractions import Fraction
from itertools import product
from math import factorial, gcd, lcm, prod


def shifted_factorial(k, offset):
    coefficients = [1]
    for j in range(k):
        expanded = [0] * (len(coefficients) + 1)
        for m, coefficient in enumerate(coefficients):
            expanded[m] += (offset - j) * coefficient
            expanded[m + 1] += coefficient
        coefficients = expanded
    return coefficients


def column_constants(columns):
    D = lcm(*(factorial(k - 1) ** 2 for k in columns))
    branches = [(k, shifted_factorial(k, offset)) for k in columns for offset in range(k)]
    scale = lcm(*(c[1]**2 // gcd(c[1]**2, factorial(k)) for k, c in branches))
    U = prod(k ** (k - 1) for k in columns)
    V = prod((2 * factorial(k)) ** (k - 1) for k in columns)
    W = prod((2 * k) ** (k - 1) for k in columns)
    T = scale
    for k, coefficients in branches:
        c = abs(coefficients[1])
        assert D % c**2 == 0 and (factorial(k) * scale) % c**2 == 0
        v = 1
        while 2 * sum(Fraction(m * abs(coefficients[m]), v**(m-1))
                      for m in range(2, k + 1)) > c:
            v *= 2
        T = max(T, (2 * v * factorial(k) * scale + c - 1) // c)
    return tuple(v.bit_length() for v in (D, U, V, W, T))


def weight_sum(columns):
    denominator = lcm(*columns)
    return sum(
        (sum(e * (denominator // k) for e, k in zip(exponents, columns))
         + denominator - 1) // denominator
        for exponents in product(*(range(k) for k in columns))
    )


def height(P, ceiling_sum, logs, M, N):
    d, u, v, w, t = logs
    Q = (P - 1) * N
    L = P * (N - M + 1) - ceiling_sum
    assert M >= 1 and L > Q
    jets = u + N * t
    excess = L - Q
    coeff = (Q * ((3 * L).bit_length() + jets) + excess - 1) // excess
    common = L.bit_length() + coeff
    norm = 2 + P * (P.bit_length() + common + v)
    real = N * d + common + w
    return max(norm, (real + M - 1) // M), norm, real


def example(columns, M):
    P = prod(columns)
    logs = column_constants(columns)
    ceiling_sum = weight_sum(columns)
    base = P * (M - 1) + ceiling_sum
    assert base + 1 >= M + len(columns)
    # Only this displayed finite interval is optimized.
    bound, N, norm, real = min(
        (bound, N, norm, real)
        for N in range(base + 1, 3 * base + 1)
        for bound, norm, real in [height(P, ceiling_sum, logs, M, N)]
    )
    return N, bound, norm, real


def seventy_primes():
    columns = (5, 7)
    M, N = 24, 863
    _, norm, real = height(prod(columns), weight_sum(columns), column_constants(columns), M, N)
    assert (norm, real) == (1554751662, 44437792)
    # The common bound for both four-column patterns is < 2^7 a^(1/36).
    assert (7 * 35519)**36 < (2**7)**36 * 10**128
    assert 36*M - N == 1
    cutoff = max(norm, 36*(real + 7*N) + 1)
    assert cutoff == 1599977989
    return cutoff


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    for columns in ((3, 5), (5, 8), (3, 5, 7, 8), (5, 6, 7, 8)):
        for M in (1, 4, 8):
            N, bound, norm, real = example(columns, M)
            print(f"{columns} M={M} N={N} H={bound} norm={norm} real={real}")
    print("Two distinct primes in every (5,7) cell of either pattern above 2^H, H =", seventy_primes())
