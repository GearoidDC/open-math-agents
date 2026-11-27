"""Check the column graph for a >= 10^100 with at most 13 distinct primes.

This step assumes that empty hosts have been excluded in columns 13 and 14.
For pairs (5,7), (5,8), and (12,13), it also assumes that a singleton host
in the larger column cannot have prime base <= that column. Those finite
exceptional-row checks are separate mathematical inputs.
"""

from functools import cache
from itertools import combinations
from math import comb, factorial, gcd


X = 10**100
PUBLISHED = {(2,3), (2,4), (2,5), (2,6), (2,8),
             (3,4), (3,6), (4,6), (4,8)}
LARGE_BASE_ONLY = {(5,7), (5,8), (12,13)}
GENERAL = {(9,10), (9,11), (9,12), (9,13), (10,11),
           (10,12), (10,13), (11,12), (11,13), (7,8)}


def root(n, k):
    low, high = 0, 1 << ((n.bit_length() + k - 1) // k)
    while low + 1 < high:
        mid = (low+high)//2
        if mid**k <= n:
            low = mid
        else:
            high = mid
    assert low**k <= n < high**k
    return low


@cache
def divisors_of_factorial(d):
    fact = factorial(d)
    base = [1]
    for p in (2,3,5,7,11,13):
        powers = [1]
        while fact % p == 0:
            fact //= p
            powers.append(p*powers[-1])
        base = [v*q for v in base for q in powers]
    assert fact == 1
    return sorted(base)


def minimum_cofactor(j,d,s,p):
    """Lower bound on b when n-s=bP is a singleton. p=0 means base > d."""
    Rj, Rd = root(factorial(j)*X,j), root(factorial(d)*X,d)
    admissible = divisors_of_factorial(d)
    thresholds = []
    for r in range(j):
        A = factorial(j) * factorial(s) * factorial(d-1-s)
        B = factorial(d) * factorial(r) * factorial(j-1-r)
        same_sign = (d-s-j+r) % 2 == 0
        left, right = A*(Rd+d-s), B*(Rj+j-r)
        if same_sign and B*(Rj-r) <= left:
            thresholds.append(1)
            continue
        # y=a/X>=1. The absolute signed difference is <=H*y^(1/j).
        # After cancellation of the p-free common factor it is a nonzero
        # multiple of P^2. Since 2/d>1/j, b^2*H >= (Rd-s)^2.
        H = max(left,right) if same_sign else left+right
        g = gcd(A,B)
        while p and g % p == 0:
            g //= p
        assert H % g == 0
        H //= g
        thresholds.append(next((v for v in admissible if v*v*H >= (Rd-s)**2), factorial(d)+1))
    return min(thresholds)


def product_bound(j,d,all_large):
    # Distinct small prime bases are assigned to distinct hosts. Class 0
    # can repeat because it covers every base greater than d.
    small = [] if all_large else [p for p in (2,3,5,7,11,13) if p<=d]
    target_count = 2*d-13
    best = {(0,0):1}
    for s in range(d):
        costs = [minimum_cofactor(j,d,s,p) for p in [0,*small]]
        updated = dict(best)
        for (count,mask), prior in best.items():
            if count >= target_count:
                continue
            for c,value in enumerate(costs):
                bit = (1 << (c-1)) if c else 0
                if mask & bit:
                    continue
                key = (count+1,mask|bit)
                updated[key] = min(updated.get(key,prior*value),prior*value)
        best = updated
    return min(value for (count,_),value in best.items() if count == target_count)


if __name__ == '__main__':
    N = root(X,13)
    assert comb(N,15) > N**13
    # Above N, C(n,15)/n^13 = n^2/15! * product(1-i/n) is increasing.
    assert all(root(factorial(d)*X,d)-d+1 > factorial(d) for d in range(2,13))
    edges = PUBLISHED.copy()
    for j,d in sorted(LARGE_BASE_ONLY | GENERAL):
        assert d < 2*j and d <= 13
        result = product_bound(j,d,(j,d) in LARGE_BASE_ONLY)
        assert result > factorial(d)
        edges.add((j,d))
        print(f"({j},{d}): cofactor product >= {result} > {d}!")
    possible = [cols for cols in combinations(range(2,14),4)
                if all(pair not in edges for pair in combinations(cols,2))]
    assert possible == []
    print("No admissible four-column sets in 2..13 under the stated hypotheses.")
