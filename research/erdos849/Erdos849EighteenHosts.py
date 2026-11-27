"""Verify the large-column cases for at most eighteen distinct prime divisors."""

from itertools import combinations
from math import comb, factorial, gcd, prod

from Erdos849EighteenPrimes import row_bounds
from Erdos849FourteenBound import floor_root
from Erdos849SingletonCertificate import factorial_divisors
from Erdos849TwelfthPower import equal_in_column


HEIGHT = 10**128


def empty_terms():
    for k in range(7, 21):
        partners = (18,) if k < 18 else range(7, k)
        low, _ = row_bounds(k, HEIGHT)
        rows = {term + s for term in factorial_divisors(k) for s in range(k)
                if term + s >= low}
        tested = 0
        for n in rows:
            a = comb(n, k)
            if a >= HEIGHT:
                assert all(not equal_in_column(a, j) for j in partners), (k, n)
                tested += 1
        if tested:
            print(f"Column {k}: {tested} possible empty-term rows excluded.")


def difference(n, j, b, c, r, offsets):
    m_num = b * prod(n - s for s in offsets) + c * r
    return (factorial(j) * c**j * prod(n - i for i in range(18))
            - factorial(18) * prod(m_num - c * i for i in range(j)))


def exclude_substitution(j, b, c, r, offsets, lo):
    q = len(offsets)
    # The ratio of falling products is strictly increasing from lo onward.
    assert j*q*lo**q < 18*((lo - 17)**q - 17*c)
    left, right = lo, lo
    while difference(right, j, b, c, r, offsets) < 0:
        right *= 2
    while left < right:
        middle = (left + right) // 2
        if difference(middle, j, b, c, r, offsets) < 0:
            left = middle + 1
        else:
            right = middle
    assert difference(left, j, b, c, r, offsets) != 0, (j, b, c, r, offsets, left)


def occupied_terms():
    ld, ud = row_bounds(18, HEIGHT)
    assert difference(18, 8, 1, 1, 6, (16, 17)) == 0
    assert difference(18, 17, 1, 1, 16, (17,)) == 0
    total = 0
    for j in range(7, 18):
        lj, uj = row_bounds(j, HEIGHT)
        q = 2 if j <= 9 else 1
        if q == 2:
            assert lj > factorial(j)*ud
        guaranteed = (q + 1)*j - 18
        assert guaranteed > 0 and j*q <= 18
        bmax = floor_root(factorial(j), guaranteed)
        cmax = bmax * ud**q // lj
        branches = 0
        for b in range(1, bmax + 1):
            for c in range(1, cmax + 1):
                if gcd(b, c) != 1 or b*ud**q < c*lj:
                    continue
                if j*q == 18:
                    # All height powers cancel. The second endpoint excludes the ratio.
                    assert b*ld**q > c*uj
                    continue
                for r in range(j):
                    for offsets in combinations(range(18), q):
                        exclude_substitution(j, b, c, r, offsets, ld)
                        branches += 1
        total += branches
        print(f"Columns ({j},18): b<={bmax}, c<={cmax}, {branches} substitutions.")
    return total


def main():
    _, upper = row_bounds(21, HEIGHT)
    assert upper**18 < HEIGHT
    empty_terms()
    print(f"Total monotone substitutions: {occupied_terms()}.")


if __name__ == "__main__":
    main()
