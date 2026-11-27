"""Exact certificate for prime-factor lower bounds on five-row values.

See Erdos849-prime-bounds.txt for the proof of the finite inequalities.
Use --cap W --power K to check all a >= 10^K with at most W primes.
"""

import argparse
from functools import lru_cache
from math import comb, factorial, gcd, isqrt
from Erdos849FourteenBound import floor_root, prime_free_part


@lru_cache(None)
def factorial_divisors(d):
    values = [1]
    q = factorial(d)
    for p in range(2, d+1):
        if q%p:
            continue
        old = values[:]
        power = 1
        while q % p == 0:
            q //= p
            power *= p
            values.extend(v*power for v in old)
    assert q == 1
    return sorted(values)


def required_cofactors(j, d, X):
    assert 2 <= j < d < 2*j and d <= 16
    roots = {k: floor_root(factorial(k)*X, k) for k in (j,d)}
    primes = [p for p in (2,3,5,7,11,13) if p <= d]
    rows = []
    for s in range(d):
        necessary = []
        for p in [*primes, None]:
            min_bound = factorial(d)
            for r in range(j):
                A = factorial(j)*factorial(s)*factorial(d-1-s)
                B = factorial(d)*factorial(r)*factorial(j-1-r)
                agree = (d-1-s)%2 == (j-1-r)%2
                # y=a/X>=1. Row minus offset is bounded between
                # (root-offset)*y^(1/k) and (root+k-offset)*y^(1/k).
                left = A*(roots[d]+d-s)
                right = B*(roots[j]+j-r)
                if agree and B*(roots[j]-r) <= left:
                    min_bound = 0
                    break
                H = max(left,right) if agree else left+right
                common = gcd(A,B)
                divisor = prime_free_part(common,p) if p else common
                assert H%divisor == 0
                H //= divisor
                # Nonzero signed difference implies P² <= H*y^(1/j).
                # Since 2j>d, a singleton with n-s=bP requires b²H >= (root-s)².
                small = isqrt(((roots[d]-s)**2-1)//H)
                min_bound = min(min_bound,small)
            necessary.append(next((v for v in factorial_divisors(d) if v>min_bound),factorial(d)+1))
        rows.append(necessary)
    return primes, rows


def minimum_product(rows, singleton_count):
    """Minimize over offsets and distinct small prime bases; large bases can repeat as a class."""
    costs = {(0,0):1}
    for bounds in rows:
        updated = costs.copy()
        for (count,used), previous in costs.items():
            if count == singleton_count:
                continue
            for i, bound in enumerate(bounds):
                bit = 0 if i == len(bounds)-1 else 1<<i
                if bit & used:
                    continue
                key = count+1, used|bit
                value = previous*bound
                if key not in updated or value<updated[key]:
                    updated[key] = value
        costs = updated
    return min(v for (count,_),v in costs.items() if count == singleton_count)


def check(w, power, verbose=False):
    X = 10**power
    N = floor_root(X,w)
    # C(n,t)/n^w = n^(t-w) * product(1-i/n)/t! is increasing for n>=t>w.
    # Above X, every represented row satisfies n>=N since a<=n^w.
    t = next(t for t in range(w+1, 20) if N >= 2*t and comb(N,t)>N**w)
    failures = []
    comparisons = 0
    for d in range(8,t):
        min_term = floor_root(factorial(d)*X,d)-d+1
        assert min_term > 0
        for j in range(7,d):
            if d >= 2*j or d > 14:
                failures.append((j,d,"outside the estimate"))
                continue
            _, rows = required_cofactors(j,d,X)
            for empty in range(max(0,d-w),d+1):
                empty_product = min_term**empty
                if empty_product > factorial(d):
                    break
                singles = max(0,2*(d-empty)-w)
                lower = empty_product * minimum_product(rows,singles)
                comparisons += 1
                if verbose:
                    print(f"j={j}, d={d}, empty={empty}: cofactor product >= {lower}, d!={factorial(d)}")
                if lower <= factorial(d):
                    failures.append((j,d,empty))
    if verbose:
        print(f"columns below {t}; {comparisons} cofactor checks; unresolved cases {failures}")
    return failures


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cap", type=int, choices=range(10,14), default=11)
    parser.add_argument("--power", type=int, default=100)
    args = parser.parse_args()
    if args.power < 100:
        parser.error("power must be at least 100 for these published pair exclusions and bounds")
    raise SystemExit(bool(check(args.cap,args.power,True)))
