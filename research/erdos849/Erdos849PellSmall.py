"""Bounded primitive Pell solutions and 100-smooth neighbors for small radicands."""

import argparse
from functools import lru_cache
from math import gcd, isqrt


PRIMES = tuple(n for n in range(2, 101)
               if all(n % d for d in range(2, isqrt(n) + 1)))


def smooth(n):
    assert n > 0
    for p in PRIMES:
        while n % p == 0:
            n //= p
    return n == 1


def supported_radicand(d):
    for p in PRIMES:
        if d % p == 0:
            d //= p
            if d % p == 0:
                return False
    return d == 1


@lru_cache(maxsize=24000)
def local_coordinates(d, h, A, B):
    """Primitive coordinates (a,b) for the specified convergent basis."""
    result = []
    bmax = 1 + isqrt(h**4 // (4*d))
    for b in range(-bmax, bmax+1):
        delta = d*b*b + A*h*h
        if delta < 0:
            continue
        v = isqrt(delta)
        if v*v != delta:
            continue
        for root in (v, -v) if v else (0,):
            numerator = root-B*b
            if numerator % A == 0:
                a = numerator // A
                if gcd(a,b) == 1:
                    result.append((a,b))
    return result


def primitive_solutions(d, hs=(1,2,3,5,7), y_limit=1 << 2100):
    """Yield (x,y,h) with positive x,y, gcd(x,y)=1, y<y_limit and x²−dy²=h²."""
    assert d >= 1 and y_limit > 0 and all(h > 0 for h in hs)
    a0 = isqrt(d)
    if a0*a0 == d:
        for h in hs:
            for u in range(1,h):
                if h*h % u == 0:
                    v = h*h//u
                    if (v+u)%2 == 0 and (v-u)%(2*a0) == 0:
                        x, y = (v+u)//2, (v-u)//(2*a0)
                        if 0 < y < y_limit and gcd(x,y) == 1:
                            yield x,y,h
        return
    # (p/q, previous_p/previous_q) is a unimodular basis.  A, B, C
    # are its quadratic form coefficients for x²−d y², with middle term 2B.
    m, den, digit = 0, 1, a0
    p, q, previous_p, previous_q = a0, 1, 1, 0
    A, B, C = a0*a0-d, a0, 1
    while q < y_limit:
        m = den*digit-m
        den = (d-m*m)//den
        digit = (a0+m)//den
        next_q = digit*q + previous_q
        stop = min(next_q, y_limit)
        if q < stop:
            for h in hs:
                for a,b in local_coordinates(d,h,A,B):
                    y = a*q+b*previous_q
                    if q <= y < stop:
                        x = a*p+b*previous_p
                        if x > 0:
                            yield x,y,h
        previous_p, p = p, digit*p+previous_p
        previous_q, q = q, next_q
        A, B, C = digit*digit*A+2*digit*B+C, digit*A+B, A


def smooth_gap_pairs(min_d=1, max_d=2401, y_limit=1 << 2100):
    """Yield all (low,high) from primitive gaps 3,5,6,7, including multiples up to gap 7."""
    for d in range(min_d, max_d+1):
        if not supported_radicand(d):
            continue
        hs = tuple(p for p in (3,5,7) if pow(d % p, (p-1)//2, p) == 1)
        if not hs:
            continue
        for x,y,h in primitive_solutions(d,hs,y_limit):
            if x % 2 == 0 and h != 3:
                continue
            if not smooth(y):
                continue
            if x % 2:
                low, high = (x-h)//2, (x+h)//2
            else:
                low, high = x-h, x+h
            assert gcd(low,high) == 1 and x*x-d*y*y == h*h
            for scale in range(1, 7//(high-low)+1):
                yield scale*low, scale*high


def controls():
    hs = (1,2,3,5,7)
    for d in range(1, 111):
        direct = set()
        for y in range(1, 650):
            for h in hs:
                n = d*y*y+h*h
                x = isqrt(n)
                if x*x == n and gcd(x,y) == 1:
                    direct.add((x,y,h))
        obtained = list(primitive_solutions(d,hs,650))
        assert len(set(obtained)) == len(obtained) and set(obtained) == direct, d
    pairs = set(smooth_gap_pairs(1,2401,1200))
    for low in range(1,300):
        for e in (3,5,6,7):
            high = low+e
            if not (smooth(low) and smooth(high)):
                continue
            divisor = gcd(low,high)
            u, v = low//divisor, high//divisor
            if v-u not in (3,5,6,7):
                continue
            d, z = u*v, 1
            for p in PRIMES:
                while d % (p*p) == 0:
                    d //= p*p
                    z *= p
            if d <= 2401:
                assert (low,high) in pairs


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, default=2100)
    args = parser.parse_args()
    controls()
    pairs = set(smooth_gap_pairs(y_limit=1 << args.bits))
    last = max(pairs)
    print(f"{len(pairs)} distinct smooth pairs for D <= 2401 and y < 2^{args.bits}.")
    print(f"Largest by lower endpoint: {last}.")
