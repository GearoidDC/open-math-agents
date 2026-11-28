"""Certify the possible index classes for all eighth-column squareclass Pell orbits."""

from collections import Counter
from functools import cache
from itertools import combinations, product
from math import comb, isqrt

from Erdos849SquareClassRows import CLASSES, WHEEL, moduli, orbits, repetitions, residue_mask, unit


def small_indices(orbit):
    """Find every signed index with row 0 through 8 or row 15."""
    i, _, d, _, D, x, y = orbit
    u, v = unit(D)
    result = set()
    for direction in (-1, 1):
        if direction == 1:
            k, xx, yy = 0, x, y
        else:
            k, xx, yy = -1, u*x-D*v*y, u*y-v*x
        assert xx > 0 and direction*yy >= 0 and (direction > 0 or yy < 0)
        while xx*xx//d + i <= 15:
            assert xx % d == 0
            n = xx*xx//d + i
            if n <= 8 or n == 15:
                m = 0 if n < 8 else (7 if n == 8 else 15)
                assert comb(n, 8) == comb(m, 7)
                result.add(k)
            xx, yy = u*xx+direction*D*v*yy, direction*v*xx+u*yy
            k += direction
    return result


def initial(orbit):
    bits = (1 << WHEEL)-1
    for p, allowed, period in moduli(orbit[4], (7,)):
        if WHEEL % period:
            break
        bits &= residue_mask(orbit, p, allowed, period)*repetitions(period, WHEEL)
        if not bits:
            break
    residues = set()
    while bits:
        low = bits & -bits
        residues.add(low.bit_length()-1)
        bits ^= low
    return residues


def modular_unit(D, p, k):
    """The coordinates of the kth power of the chosen Pell unit modulo p."""
    a, b = 1, 0
    u, v = unit(D)
    while k:
        if k & 1:
            a, b = (a*u+D*b*v) % p, (a*v+b*u) % p
        k //= 2
        u, v = (u*u+D*v*v) % p, 2*u*v % p
    return a, b


@cache
def possible_rows(p):
    image = {comb(m, 7) % p for m in range(p)}
    return frozenset(n for n in range(p) if comb(n, 8) % p in image)


def period_filter(orbit, indices, period, p):
    i, _, d, _, D, x, y = orbit
    assert modular_unit(D, p, period) in ((1, 0), (p-1, 0))
    allowed = possible_rows(p)
    inverse = pow(d, -1, p)
    good = []
    for k in indices:
        u, v = modular_unit(D, p, k)
        xx = (u*x+D*v*y) % p
        if (xx*xx*inverse+i) % p in allowed:
            good.append(k)
    return good


def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n)+1))


EXTRA_PRIMES = tuple(p for p in range(11, 40001) if is_prime(p)) + (49279,)
MULTIPLIERS = (2, 4, 6, 8, 9, 12, 16, 13)


@cache
def period_primes(D, modulus):
    return frozenset(p for p in EXTRA_PRIMES
                     if modular_unit(D, p, modulus) in ((1, 0), (p-1, 0)))


def reduce_indices(orbit, residues, period, allowed_primes):
    for p in sorted(allowed_primes):
        residues = period_filter(orbit, residues, period, p)
        if not residues:
            break
    return residues


def directly_realized_pairs():
    result = set()
    for n in (*range(9), 15):
        options = {}
        for i in range(min(n+1, 8)):
            options[i] = [d for d in CLASSES if (n-i) % d == 0
                          and isqrt((n-i)//d)**2 == (n-i)//d]
        for i, j in combinations(options, 2):
            result.update((i, j, d, e) for d, e in product(options[i], options[j]) if d != e)
    return result


def recurrence_control():
    # Compare direct forward iteration, including the indices on the far
    # side of a period, with modular powering and the column-image test.
    o = (3, 4, 3, 2, 6, 3, 1)
    i, _, d, _, D, x, y = o
    p = 127
    u, v = unit(D)
    a, b = 1, 0
    period = 2
    while modular_unit(D, p, period) not in ((1, 0), (p-1, 0)):
        period += 1
    indices = list(range(3*period))
    expected = []
    for k in indices:
        assert (a, b) == modular_unit(D, p, k)
        n = ((a*x+D*b*y)**2*pow(d, -1, p)+i) % p
        if any((comb(n, 8)-comb(m, 7)) % p == 0 for m in range(p)):
            expected.append(k)
        a, b = (u*a+D*v*b) % p, (v*a+u*b) % p
    assert 0 < len(expected) < len(indices)
    assert expected == period_filter(o, indices, period, p)


def verify():
    if not __debug__:
        raise RuntimeError("This verifier uses assertions.")
    assert is_prime(49279) and WHEEL == 27720
    recurrence_control()
    orbit_list = tuple(orbits())
    assert len(orbit_list) == len(set(orbit_list)) == 928
    initial_zero = 0
    allowed_pairs = set()
    index_sets = Counter()
    for orbit in orbit_list:
        D = orbit[4]
        signed = small_indices(orbit)
        index_sets[tuple(sorted(signed))] += 1
        target = {i % WHEEL for i in signed}
        start = initial(orbit)
        assert target <= start
        if not start:
            initial_zero += 1
        remaining = start-target
        if remaining:
            base = period_primes(D, WHEEL)
            remaining = reduce_indices(orbit, remaining, WHEEL, base)
        if remaining:
            for multiplier in MULTIPLIERS:
                modulus = multiplier*WHEEL
                lifts = [r+j*WHEEL for r in remaining for j in range(multiplier)]
                surviving = reduce_indices(orbit, lifts, modulus, period_primes(D, modulus)-base)
                remaining = {i % WHEEL for i in surviving}
                if not remaining:
                    break
        assert not remaining, (orbit, remaining)
        if target:
            allowed_pairs.add(orbit[:4])
    assert index_sets == {():398, (0,):437, (-1,):25, (-1,0):60, (-1,0,1):8}
    assert initial_zero == 360 and len({o[:4] for o in orbit_list}) == 836
    assert allowed_pairs == directly_realized_pairs() and len(allowed_pairs) == 505
    high = {(i,j,d,e) for i,j,d,e in allowed_pairs if min(d,e) > 7}
    assert high == {(0,1,15,14), (0,5,15,10), (1,5,14,10)}
    assert all(d <= 15 for i,j,d,e in allowed_pairs)
    assert all(e <= 15 or d*isqrt((j-i)//d)**2 == j-i for i,j,d,e in allowed_pairs)
    print("398 of 928 orbits excluded at every index. "
          "All 606 surviving orbit/residue pairs modulo 27720 contain a small row.")
    print("505 of 836 offset/class choices survive; exactly three have both classes above seven.")


if __name__ == "__main__":
    verify()
