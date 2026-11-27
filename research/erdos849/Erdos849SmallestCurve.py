"""Finite-branch and map-degree checks for the fixed columns 3, 5, 7, 8."""

from itertools import combinations, product
from math import factorial, prod

from Erdos849ThreeFiveCurve import gcd, mul, prime, remainder


def resultant(f, g, p):
    if len(g) == 1:
        return pow(g[0], len(f) - 1, p)
    r = remainder(f, g, p)
    if not r:
        return 0
    sign = (-1) ** ((len(f) - 1) * (len(g) - 1))
    return sign * pow(g[-1], len(f) - len(r), p) * resultant(g, r, p) % p


def critical_polynomial(k, p):
    f = [1]
    for s in range(k):
        f = mul(f, [-s % p, 1], p)
    derivative = [i * f[i] % p for i in range(1, len(f))]
    out = [0] * k
    # Evaluate at k arguments and interpolate the polynomial of degree k-1.
    for t in range(k):
        ft = [(f[0] - factorial(k) * t) % p, *f[1:]]
        basis, denom = [1], 1
        for v in range(k):
            if v != t:
                basis = mul(basis, [-v % p, 1], p)
                denom = denom * (t - v) % p
        value = resultant(ft, derivative, p) * pow(denom, -1, p) % p
        for i, c in enumerate(basis):
            out[i] = (out[i] + c * value) % p
    return [c * pow(out[-1], -1, p) % p for c in out]


def genus(degrees):
    d = prod(degrees)
    return (d * (len(degrees) - 1) - sum(d // k for k in degrees) + 1) // 2


def smaller(degrees):
    for k in degrees:
        sub = tuple(d for d in degrees if d != k)
        if k == 8:
            yield 2, tuple(sorted((*sub, 4)))
        else:
            yield k, sub


def primitive_bound(degrees, h):
    g = genus(degrees)
    if g < h:
        return None
    bound = 1
    if degrees == (7, 8):
        # Smooth plane octic. See the adjunction/interpolation proof in the note.
        bound = {0: 7, 1: 5}.get(h, 1)
    for k, sub in smaller(degrees):
        num = g - k * genus(sub) + k - 1
        den = h + k - 1
        bound = max(bound, -(-num // den))
    if h > 1 and bound * (h - 1) > g - 1:
        return None
    return bound


if __name__ == '__main__':
    for p in range(11, 300):
        if prime(p):
            delta = [critical_polynomial(k, p) for k in (3, 5, 7, 8)]
            if all(len(gcd(f, g, p)) == 1 for f, g in combinations(delta, 2)):
                break
    else:
        raise AssertionError('no witness prime')
    print('finite branch polynomials, ascending coefficients mod', p, delta)
    intermediate = [tuple(sorted(k for k in choice if k)) for choice in
                    product((0, 3), (0, 5), (0, 7), (0, 4, 8))]
    assert genus((3, 5, 7, 8)) == 924 and genus((3, 4, 5, 7)) == 436
    for h in (0, 1, 2):
        candidates = []
        for degrees in intermediate:
            b = primitive_bound(degrees, h)
            if b is not None:
                candidates.append((840 // prod(degrees) * b, degrees, b))
        bound = min(v[0] for v in candidates)
        print('target genus', h, 'lower bound', bound,
              'attained as a bound at', [c for c in candidates if c[0] == bound])
