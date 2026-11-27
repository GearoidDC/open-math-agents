"""Restrict pairs of square classes in an eighth-column numerator via Pell orbits."""

from functools import cache
from itertools import combinations, product
from math import comb, gcd, isqrt

from Erdos849PatternThreeCRT import row_in_column
from Erdos849Wheel import allowed_moduli


CLASSES = tuple(d for d in range(1, 211) if 210 % d == 0)
WHEEL = 27720
END = 210000


@cache
def unit(D):
    for v in range(1, 1000):
        u = isqrt(1 + D*v*v)
        if u*u - D*v*v == 1:
            return u, v
    raise ValueError(D)


@cache
def seeds(D, norm):
    _, v = unit(D)
    result = []
    for y in range(isqrt(v*v*norm - 1) + 1):
        x = isqrt(D*y*y + norm)
        if x*x - D*y*y == norm:
            result.append((x, y))
    return tuple(result)


def orbits():
    for i, j in combinations(range(8), 2):
        for d, e in product(CLASSES, repeat=2):
            if d == e:
                continue
            g = gcd(d, e)
            D = d*e//(g*g)
            for x, y in seeds(D, d*(j-i)):
                if x % d == 0 and y % g == 0:
                    yield i, j, d, e, D, x, y


@cache
def period(D, p):
    u, v = unit(D)
    x, y = 1, 0
    for length in range(1, 2*p+1):
        x, y = (u*x+D*v*y) % p, (v*x+u*y) % p
        if (x, y) == (1, 0):
            return length
    raise AssertionError((D, p))


def residue_mask(orbit, p, allowed, length):
    i, _, d, _, D, x, y = orbit
    u, v = unit(D)
    inv = pow(d, -1, p)
    mask = 0
    for k in range(length):
        if (x*x*inv+i) % p in allowed:
            mask |= 1 << k
        x, y = (u*x+D*v*y) % p, (v*x+u*y) % p
    return mask


@cache
def repetitions(period_length, total):
    blocks = (total+period_length-1)//period_length
    return ((1 << (blocks*period_length))-1)//((1 << period_length)-1)


@cache
def moduli(D, columns):
    primes = [(p, frozenset(rows), period(D, p)) for p, rows in allowed_moduli(8, columns)]
    return sorted(primes, key=lambda m: (WHEEL % m[2] != 0, m[0]))


def screen(orbit, columns):
    D = orbit[4]
    mods = moduli(D, columns)
    wheel = (1 << WHEEL)-1
    for p, good, length in mods:
        if WHEEL % length:
            break
        wheel &= residue_mask(orbit, p, good, length)*repetitions(length, WHEEL)
        if not wheel:
            return False, []
    finite = (wheel*repetitions(WHEEL, END)) & ((1 << END)-1)
    for p, good, length in mods:
        if WHEEL % length:
            finite &= residue_mask(orbit, p, good, length)*repetitions(length, END)
            if finite.bit_length() <= 100:
                break
    indices = []
    while finite:
        lowbit = finite & -finite
        indices.append(lowbit.bit_length()-1)
        finite ^= lowbit
    return True, indices


def power(D, x, y, k):
    u, v = unit(D)
    while k:
        if k % 2:
            x, y = u*x+D*v*y, v*x+u*y
        u, v = u*u+D*v*v, 2*u*v
        k //= 2
    return x, y


def check_controls():
    limit = 3000
    direct = set()
    by_value = {d*u*u:d for d in CLASSES for u in range(isqrt(limit//d)+1) if u}
    for n in range(16, limit+1):
        for i, j in combinations(range(8), 2):
            d, e = by_value.get(n-i), by_value.get(n-j)
            if d and e and d != e:
                direct.add((n,i,j,d,e))
    generated = set()
    for i,j,d,e,D,x,y in orbits():
        u, v = unit(D)
        while x*x//d+i <= limit:
            n = x*x//d+i
            assert n-j == e*(y//gcd(d,e))**2 and x % d == y % gcd(d,e) == 0
            if n >= 16:
                generated.add((n,i,j,d,e))
            x, y = u*x+D*v*y, v*x+u*y
    assert direct and direct == generated
    # Equal square classes force n <= 56 from the difference of two squares.
    assert not any(row_in_column(comb(n,8),7) for n in range(16,57))
    # For k >= END, x >= 2^k and n >= 4^k/210.
    assert 4**END >= 2940 and 4**(8*END) > 40320*420**8*10**1000000


def verify(columns):
    orbit_count = global_exclusions = exact_checks = largest_index = 0
    pairs = set()
    possible_pairs = set()
    matches = set()
    for orbit in orbits():
        i,j,d,e,D,x,y = orbit
        pair = (i,j,d,e)
        pairs.add(pair)
        possible, indices = screen(orbit, columns)
        orbit_count += 1
        if not possible:
            global_exclusions += 1
            continue
        possible_pairs.add(pair)
        for index in indices:
            exact_checks += 1
            largest_index = max(largest_index,index)
            xx, yy = power(D,x,y,index)
            n = xx*xx//d+i
            assert n-j == e*(yy//gcd(d,e))**2
            if n >= 16:
                a = comb(n,8)
                if all(row_in_column(a,k) for k in columns):
                    matches.add(n)
    assert not matches, matches
    if len(columns) == 3:
        # Zero square values are allowed at these small, inadmissible rows.
        def is_square_multiple(m, d):
            return m >= 0 and m % d == 0 and isqrt(m//d)**2 == m//d
        trivial_pairs = {(i,j,d,e) for i,j,d,e in pairs
                         if any(is_square_multiple(n-i,d) and is_square_multiple(n-j,e)
                                for n in range(1,9))}
        assert len(trivial_pairs) == 492 and trivial_pairs == possible_pairs
    print(columns, "orbits", orbit_count, "excluded at every height", global_exclusions,
          "represented pairs", len(pairs), "remaining pairs", len(possible_pairs),
          "exact indices", exact_checks, "largest index", largest_index, flush=True)


if __name__ == "__main__":
    check_controls()
    for columns in ((7,), (3,5,7), (5,6,7)):
        verify(columns)
