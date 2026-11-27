"""Check every pair 7 <= j < d with d >= 19 under a cap of twenty prime bases."""

from itertools import combinations
from math import comb, factorial, gcd, lcm

from Erdos849NineteenHosts import X, divisors, floor_root, row_bounds, sign
from Erdos849TwelfthPower import equal_in_column


def empty_terms():
    totals = []
    for k in range(7, 24):
        partners = {19, 20} if k < 19 else set(range(7, k))
        if k == 19:
            partners.add(20)
        lo, _ = row_bounds(k, X)
        candidates = {cofactor + s for cofactor in divisors(lcm(*range(1, k + 1)))
                      for s in range(k) if cofactor + s >= lo}
        tested = 0
        for n in candidates:
            a = comb(n, k)
            if a >= X:
                assert all(not equal_in_column(a, j) for j in partners), (n, k)
                tested += 1
        totals.append(tested)
    return totals


def potential_ratios(j, d):
    lj, uj = row_bounds(j, X)
    ld, ud = row_bounds(d, X)
    mj = lcm(*range(1, j + 1))
    q = 1
    while j*q <= d and lj > mj*ud**q:
        q += 1
    if j*q > 20:
        return q, []
    clean = (q + 1)*j - 20 - 2*(20 - d)
    assert clean > 0
    if j*q <= d:
        bmax = floor_root(factorial(j), clean)
        cmax = bmax*ud**q // lj
    else:
        cmax = floor_root(factorial(d), clean)
        bmax = cmax*uj // ld**q
    ratios = []
    for b in divisors(mj):
        if b > bmax:
            continue
        for c in range(1, cmax + 1):
            if factorial(d) % c or gcd(b, c) != 1:
                continue
            if j*q <= d and b*ud**q < c*lj:
                continue
            if j*q >= d and b*ld**q > c*uj:
                continue
            ratios.append((b, c))
    assert j*q != d or not ratios
    return q, ratios


def no_root(d, j, b, c, r, offsets, lo):
    q = len(offsets)
    increasing = d > j*q
    if increasing:
        assert j*q*lo**q < d*((lo - d + 1)**q - j*c)
    else:
        assert d*(lo**q + j*c) < j*q*(lo - d + 1)**q
    direction = 1 if increasing else -1
    left = right = lo
    while direction*sign(right, d, j, b, c, r, offsets) < 0:
        right *= 2
    while left < right:
        middle = (left + right) // 2
        if direction*sign(middle, d, j, b, c, r, offsets) < 0:
            left = middle + 1
        else:
            right = middle
    return sign(left, d, j, b, c, r, offsets) != 0


def occupied_terms(j, d):
    low, _ = row_bounds(d, X)
    q, ratios = potential_ratios(j, d)
    count = 0
    for b, c in ratios:
        for r in range(j):
            for offsets in combinations(range(d), q):
                assert no_root(d, j, b, c, r, offsets, low), (d, j, b, c, r, offsets)
                count += 1
    return count


def main():
    assert row_bounds(24, X)[1]**20 < X
    assert sign(20, 20, 9, 1, 1, 7, (18, 19)) == 0
    assert sign(19, 19, 10, 1, 1, 8, (17, 18)) == 0
    print("Possible empty-term rows tested for columns 7–23:", empty_terms(), flush=True)
    for d in (19, 20):
        for j in range(7, d):
            print(f"Columns ({j},{d}): {occupied_terms(j, d)} substitutions.", flush=True)


if __name__ == "__main__":
    main()
