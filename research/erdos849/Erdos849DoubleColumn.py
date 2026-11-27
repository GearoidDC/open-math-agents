"""Exact arithmetic checks for the (7,14) argument in Erdos849DoubleColumn.txt.

The small-row sieve is unconditional. The larger-row list is exhaustive for
a hypothetical collision with at most fourteen prime factors by the empty-host
theorem in the accompanying note. No downloaded data or third-party packages.
"""

from fractions import Fraction
from math import comb, factorial, isqrt


ROW = 10**6
D = factorial(14)//factorial(7)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def constants():
    lo, hi = Fraction(92,1000), Fraction(93,1000)
    require(D*lo**7 < 1 < D*hi**7, "theta enclosure")
    require(lo > Fraction(1,16), "quadratic growth")
    require(ROW*(ROW-64*factorial(7)) > 6*64, "singleton contradiction")
    require(hi + Fraction(6,ROW**2) < Fraction(1,4), "pair ratio less than one")
    require(26*hi < 3, "row-ratio error")
    require(Fraction(1,11) < lo-Fraction(29,ROW), "lower Farey boundary")
    require(hi+Fraction(29,ROW) < Fraction(3,32), "upper Farey boundary")
    require(3*11-32 == 1 and 37**7 > factorial(14), "denominator gap")
    require(comb(factorial(14)+13,14) < 10**143, "height bound")


def exists_seventh_row(a):
    """Invert the strictly increasing seventh column on rows m>=14."""
    lo, hi = 13, 14
    while comb(hi,7) < a:
        lo, hi = hi, hi*2
    while hi-lo > 1:
        mid = (lo+hi)//2
        if comb(mid,7) < a:
            lo = mid
        else:
            hi = mid
    return comb(hi,7) == a


def residue_tests():
    tables = []
    for p in range(71,500):
        if any(p%q == 0 for q in range(2,isqrt(p)+1)):
            continue
        possible = {comb(r,7)%p for r in range(p)}
        allowed = bytes(comb(r,14)%p in possible for r in range(p))
        tables.append((sum(allowed)/p,p,allowed))
    return sorted(tables)


def small_rows():
    # Since p>14, each coefficient in question is a polynomial function of
    # the row modulo p. A missing residue certifies inequality for every m.
    tests = residue_tests()
    exact = 0
    for n in range(28,ROW):
        if all(allowed[n%p] for _,p,allowed in tests):
            exact += 1
            require(not exists_seventh_row(comb(n,14)), f"small collision, n={n}")
    return ROW-28, exact


def empty_rows():
    den = factorial(14)
    divisors = set()
    for b in range(1,isqrt(den)+1):
        if den%b == 0:
            divisors.update((b, den//b))
    candidates = {b+s for b in divisors for s in range(14) if b+s >= ROW}
    above_googol = 0
    for n in candidates:
        a = comb(n,14)
        above_googol += a>=10**100
        require(not exists_seventh_row(a), f"empty-host collision, n={n}")
    return len(divisors), len(candidates), above_googol


def main():
    constants()
    small, exact = small_rows()
    divisors, exceptional, above_googol = empty_rows()
    print(f"All rational constants checked; C(14!+13,14) < 10^143.")
    print(f"Small rows: {small} considered, {exact} exact inversions, no collision.")
    print(f"Empty hosts: {divisors} divisors of 14!, {exceptional} distinct larger rows, "
          f"all tested by exact inversion, no collision.")
    print(f"Of those larger rows, {above_googol} have value at least 10^100.")


if __name__ == "__main__":
    main()
