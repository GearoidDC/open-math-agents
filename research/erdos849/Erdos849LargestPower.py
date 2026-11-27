"""Bounds for every full prime power dividing a hypothetical five-row entry."""

from functools import cache
from math import comb, factorial, gcd

from Erdos849FourteenBound import floor_root
from Erdos849GridHeight import log_s_bound


def valuation(x, p):
    exponent = 0
    while x % p == 0:
        exponent += 1
        x //= p
    return exponent


def shifted_product(k, offset, scale):
    """Coefficients of (scale*T + offset)_k, in ascending order."""
    poly = [1]
    for v in range(k):
        nxt = [0]*(len(poly)+1)
        for i, c in enumerate(poly):
            nxt[i] += (offset-v)*c
            nxt[i+1] += scale*c
        poly = nxt
    return poly


@cache
def constant_bound(j, d, r, s):
    dscale = d*comb(d-1, s)
    jscale = j*comb(j-1, r)
    common = gcd(dscale, jscale)
    left = shifted_product(d, s, dscale//common)
    right = shifted_product(j, r, jscale//common) + [0]*(d-j)
    poly = [x*factorial(j) - y*factorial(d) for x,y in zip(left,right)]
    return abs(next(c for c in poly if c)//gcd(*poly))


@cache
def bad_denominator(k, s, p):
    return max(valuation(t,p) for t in range(1, max(s,k-1-s)+1))


def pair_check(j, d, h, x):
    rd = floor_root(factorial(d)*x, d)
    rj = floor_root(factorial(j)*x, j)
    # 0 stands for every prime larger than d.
    bases = [0]+[p for p in (2,3,5,7,11,13) if p <= d]
    assert d <= 14 and h <= 2*j and d**h < x
    zeros = 0
    for s in range(d):
        for r in range(j):
            ed, ej = d*comb(d-1,s), j*comb(j-1,r)
            common = gcd(ed,ej)
            same_sign = (d-1-s)%2 == (j-1-r)%2
            if same_sign and ed*(rj-r) <= ej*(rd+d-s):
                # A vanishing signed difference forces P to divide an
                # integer root of an explicit primitive polynomial.
                if constant_bound(j,d,r,s)**h >= x:
                    return None
                zeros += 1
            a, b = ej*(rd+d-s), ed*(rj+j-r)
            z = (max(a,b) if same_sign else a+b)//common
            for p in bases:
                loss = gain = 1
                if p:
                    vd, vj = valuation(ed,p), valuation(ej,p)
                    bonus = (max(vd,vj) +
                             min(vd-bad_denominator(d,s,p), vj-bad_denominator(j,r,p)))
                    gain, loss = p**max(0,bonus), p**max(0,-bonus)
                if (loss*z)**h >= x**2 * gain**h:
                    return None
    return zeros


def practical(h, height):
    x = 10**height
    t = h+1
    # If the largest column is >=t, compare to column t in the same row.
    root = floor_root(factorial(t)*x, t)
    if (root+t)**h >= x:
        return None
    count = 0
    for d in range(8,t):
        for j in range(7,d):
            zeros = pair_check(j,d,h,x)
            if zeros is None:
                return None
            count += zeros
    return count


def single_tuple_bound(r, d, p):
    """An upper bound on log10(a) if one tuple hosts >=a^(1/839)."""
    w = 839
    basis = min(p,1680)
    m = (2*basis*r + basis-w-1)//(basis-w)
    order = w*m
    n = basis*(m-r)
    assert n > order
    spare = n-order
    j = (order+spare-1)//spare
    log_s = log_s_bound(d)
    log_e = (order+1)*r*d*log_s
    log_c = j*(1+len(str(n))+log_e)
    log_eval = r*order*log_s+len(str(n))+log_c+r*d*len(str(2*d))
    log_norm = p*(len(str(p))+len(str(n))+log_c+r*d*log_s)
    return max(log_eval,log_norm)+1


if __name__ == "__main__":
    assert 3*839*840 < 200_000_000_000_000_000
    for h, k in ((11,128),(12,174),(13,477)):
        cases = practical(h,k)
        assert cases is not None, (h,k)
        print(f"a >= 10^{k}: P^{h} < a; exact-zero checks: {cases}")
    for r, divisor, cap in [(2,7,839),(3,35,119),(4,70,23)]:
        small = max(single_tuple_bound(r,min(cap,p//divisor),p) for p in range(840,1680))
        large = single_tuple_bound(r,cap,839**2)
        assert max(small,large) < 200_000_000_000_000_000
        print(f"Single tuple at exponent 1/839, {r} columns: {max(small,large):,}")
