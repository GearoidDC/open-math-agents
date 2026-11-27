"""Check column 18 under a cap of twenty distinct prime factors."""

from itertools import combinations
from math import factorial, gcd, lcm

from Erdos849TwentyHosts import (
    X, divisors, floor_root, no_root, occupied_terms, row_bounds,
)


def exceptional_pair(j):
    d = 18
    lj, _ = row_bounds(j, X)
    ld, ud = row_bounds(d, X)
    mj = lcm(*range(1, j + 1))
    if j == 11:
        # At least two shallow terms carry one power each; their cofactors
        # have product at most 11!, and each power divides a deep term.
        assert 2*j - 20 >= 2
        assert floor_root(factorial(j), 2)*ud < lj
        return 0

    q = {8: 2, 12: 1}[j]
    assert q == 1 or lj > mj*ud**(q - 1)
    assert (q + 1)*j - 20 >= 4
    # Three affected shallow hosts would have to draw three distinct
    # powers from at most two deep terms, whose product bounds all three.
    assert 3*d >= j*(3*q - 1)
    assert lj**3 > factorial(j)*ud**(3*q - 1)
    bmax = floor_root(factorial(j), 2)
    searches = 0
    for b in divisors(mj):
        if b > bmax:
            continue
        for c in range(1, b*ud**q//lj + 1):
            if factorial(d) % c or gcd(b, c) != 1:
                continue
            for r in range(j):
                for offsets in combinations(range(d), q):
                    assert no_root(d, j, b, c, r, offsets, ld), (j,b,c,r,offsets)
                    searches += 1
    return searches


if __name__ == "__main__":
    for k in range(7, 19):
        assert lcm(*range(1, k + 1)) < row_bounds(k, X)[0]
    for j in range(7, 18):
        count = exceptional_pair(j) if j in (8, 11, 12) else occupied_terms(j, 18)
        print(f"Columns ({j},18): {count} substitutions.", flush=True)
