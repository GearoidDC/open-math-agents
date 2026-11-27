"""Check the column-pair and prime-factor inequalities for the five-row case."""

from functools import cache
from itertools import combinations
from math import comb, factorial, gcd, isqrt

from Erdos849FifteenPrimes import classify
from Erdos849FourteenBound import floor_root
from Erdos849SingletonCertificate import factorial_divisors
from Erdos849SeventeenLarge import eight_seven


def row_bounds(k, x):
    root = floor_root(factorial(k) * x, k)
    return root - k + 1, root + k


def component_obstruction(j, d, x, cap):
    """A component with h and q vertices must have compatible row products."""
    lj, uj = row_bounds(j, x)
    ld, ud = row_bounds(d, x)
    if lj <= factorial(j) or ld <= factorial(d):
        return False
    required = d + j - cap
    if required <= 1:
        return False
    possible = []
    for h in range(1, d + 1):
        for q in range(1, j + 1):
            if h*j >= q*d and ld**h > factorial(d) * uj**q:
                continue
            if q*d >= h*j and lj**q > factorial(j) * ud**h:
                continue
            if h*j == q*d and (h, q) != (d, j):
                # The height powers cancel. If the interval for the
                # d-side cofactor product has no integer for any
                # divisor J of j!, this component cannot occur.
                if not any((v*ld**h + uj**q-1)//uj**q <= v*ud**h//lj**q
                           for v in factorial_divisors(j)):
                    continue
            possible.append((h, q))

    @cache
    def can_partition(h, q, need):
        if h == 0 or q == 0:
            return h == q == 0 and need <= 0
        if min(h, q) < need:
            return False
        return any(can_partition(h-i, q-k, need-1)
                   for i, k in possible if i <= h and k <= q)

    return not can_partition(d, j, required)


def power_ceiling(x):
    """Uniform bound P <= Q*y^(1/14) for a full prime power, a=x*y."""
    j, d = 7, 8
    rj = floor_root(factorial(j)*x, j)
    rd = floor_root(factorial(d)*x, d)
    peak = 0
    for s in range(d):
        for r in range(j):
            ca = factorial(j)*factorial(s)*factorial(d-1-s)
            cb = factorial(d)*factorial(r)*factorial(j-1-r)
            if cb*(rj-r) <= ca*(rd+d-s):
                return None
            common = gcd(ca, cb)
            # Divide only by a divisor of the common factor coprime to p.
            # The smallest eligible divisor across unknown prime bases
            # results from retaining the largest prime-power part in common.
            largest = 1
            for p in (2, 3, 5, 7):
                part = 1
                while common % (part*p) == 0:
                    part *= p
                largest = max(largest, part)
            unit = common // largest
            peak = max(peak, (ca*(rd+d-s) + cb*(rj+j-r)) // unit)
    return isqrt(peak)+1


def seven_eight(power):
    x = 10**power
    q = power_ceiling(x)
    if q is None:
        return False
    l7, u7 = row_bounds(7, x)
    l8, u8 = row_bounds(8, x)
    # Three ordinary powers from three distinct paired slots: their
    # three cofactors multiply to a divisor of 8!. With a shared slot
    # the two powers there contribute their full slot product.
    triple_impossible = (l8**3 > factorial(8)*q**3*u7
                         and l8**2 > factorial(8)*q*u7)
    # The previous computation retains the distinct bases of partners.
    if not triple_impossible:
        triple_impossible = eight_seven(power)
    return (l8 > factorial(8)*q and triple_impossible
            and l7 > factorial(7)*u8
            and l7**2 > factorial(7)*q**2*u8)


def remaining(power):
    x = 10**power
    cap = 17
    n = floor_root(x, cap)
    assert n >= 36 and comb(n, 18) > n**cap
    edges = set()
    for j, d in combinations(range(2, cap+1), 2):
        if (d <= 16 and classify(j, d, x, cap) == "excluded"
                or component_obstruction(j, d, x, cap)):
            edges.add((j, d))
    if seven_eight(power):
        edges.add((7, 8))
    return [p for p in combinations(range(2, cap+1), 4)
            if edges.isdisjoint(combinations(p, 2))]


if __name__ == "__main__":
    import sys
    for k in map(int, sys.argv[1:] or [524]):
        unresolved = remaining(k)
        print(k, "seven-eight", seven_eight(k), "unresolved", unresolved, flush=True)
        if k == 524:
            assert seven_eight(k) and not unresolved
