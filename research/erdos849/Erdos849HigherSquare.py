"""Exact bounds for square products on specified simultaneous Pascal columns."""

from fractions import Fraction
from itertools import product
from math import factorial, gcd, lcm, prod


def ceil_div(a, b):
    return (a + b - 1) // b


def digits(x):
    return len(str(x))


def valuation(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def branch_check(k, radius_denominator=1000):
    delta = Fraction(1, 20)
    radius = Fraction(1, radius_denominator)
    lower = 2*k*delta - ((1+delta)**k - 1)
    upper = (1+delta+(k-1)*radius)**k - (1+delta)**k
    assert 0 < upper < lower and 1+delta+(k-1)*radius < 2


def certificate(K, multiple=7):
    d, r = K[-1], len(K)
    assert list(K) == sorted(set(K)) and 2 <= min(K) and d <= 16
    radius_denominator = 1000 if d <= 10 else 10000
    for k in K:
        branch_check(k, radius_denominator)
    E = lcm(*K)
    L = multiple*E
    weights = [E//k for k in K]
    b = weights[-1]
    fibers = prod(K)//E
    assert gcd(*weights) == 1
    # Check explicitly that every weight residue has the expected fiber size.
    hist = [0]*E
    for exponents in product(*(range(k) for k in K)):
        hist[sum(i*s for i,s in zip(exponents,weights))%E] += 1
    assert set(hist) == {fibers}

    def nmon(extra):
        count = 0
        for exponents in product(*(range(k) for k in K[:-1])):
            wt = sum(i*s for i,s in zip(exponents,weights))
            count += max(0,(L-wt)//b+1) + max(0,(L-wt-extra)//b+1)
        return count

    nmax = nmon(0)
    nmin = nmon(sum(k//2*w for k,w in zip(K,weights)))
    R = fibers*(L+1)
    assert nmin > R
    prime_set = tuple(p for p in (2,3,5,7,11,13) if p <= d)
    const_valuation = {p: sum(valuation(factorial(k),p) for k in K) for p in prime_set}
    slope = {p: max(k*valuation(4*k*k,p)+valuation(factorial(k),p) for k in K)
             for p in prime_set}

    real_bound = 2**(L//b)*factorial(d)**multiple
    arch = (1+L//b)**r * real_bound
    log_range = 0
    for h in range(L+1):
        denom = prod(p**(const_valuation[p]+h*slope[p]//E) for p in prime_set)
        height = denom*arch*radius_denominator**(h//b)
        log_range += fibers*digits(2*nmax*height+1)
    C = log_range//(nmin-R)+1
    W = C + digits(2*nmax*real_bound*radius_denominator**ceil_div(L+1,b)) + 1

    degrees = 2*prod(K[:-1])
    J = sum(2*k-1 for k in K[:-1])
    entry_scale = nmax*prod(factorial(k) for k in K)*(2*factorial(d))**J
    entry_digits = C+digits(entry_scale)
    norm_digits = digits(factorial(degrees)) + degrees*entry_digits
    height_cutoff = max(E*W, d*(norm_digits+1))
    return L, fibers, nmin, nmax, C, E*W, d*(norm_digits+1), height_cutoff


if __name__ == '__main__':
    cases = [((3,5,7,8),8,1399280), ((5,6,7,8),9,3209464),
             ((5,7,8),6,346896), ((7,9),3,49374), ((8,9),4,61479),
             ((7,10),4,63540), ((8,10),4,74870), ((9,10),4,92330)]
    for K,m,target in cases:
        data = certificate(K,m)
        assert data[-1] == target
        print(K, data)
