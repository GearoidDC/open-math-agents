"""Per-numerator-factor counts using the two published local certificates."""

from itertools import combinations
from math import comb, factorial, lcm, prod


def part(n, p):
    result = 1
    while n % p == 0:
        result *= p
        n //= p
    return result


def iroot(n, k):
    lo, hi = 0, 1 << ((n.bit_length() + k - 1) // k)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid
    return hi if hi**k == n else lo


def scale(k, s, t):
    ell = lcm(*range(1, k + 1))
    c = k * comb(k - 1, s)
    assert ell % c == 0
    return max(ell // prod(part(ell // c, p) for p in uniform)
               * prod(part(420, p) for p in uniform)
               for w in range(min(4, t) + 1)
               for uniform in combinations((2, 3, 5, 7), w))


def minima(E, Q, ks):
    for k in ks:
        floor = iroot(factorial(k) * 10**E, k)
        bounds = []
        for s in range(k):
            t = 0
            while k * t <= 36 and (scale(k, s, t) * Q**t)**36 * 10**((E-128)*t) < (floor - s)**36:
                t += 1
            bounds.append(t)
        print(E, k, bounds)


if __name__ == '__main__':
    minima(136, 34800, (3, 5, 7, 8))
    minima(144, 35519, (5, 6, 7, 8))
