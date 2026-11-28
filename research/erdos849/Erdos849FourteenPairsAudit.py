"""Independent finite check for square-class relations in individual Pascal rows."""

from fractions import Fraction
from itertools import combinations
from math import comb, factorial, isqrt, lcm, prod


def multiply(a, b):
    result = [0] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result


def positive_after(poly, start):
    # Coefficients of poly(start + Y), in order of increasing degree.
    shifted = [sum(c*comb(i,j)*start**(i-j) for i,c in enumerate(poly) if i >= j)
               for j in range(len(poly))]
    return shifted[0] > 0 and min(shifted) >= 0


def audit_even_subsets():
    exceptions = []
    largest_cutoff = 0
    for size in (2,4,6,8):
        for offsets in combinations(range(8), size):
            f = [1]
            for i in offsets:
                f = multiply(f, [-i,1])
            # Cancel the upper half of the coefficients of f-R^2.
            degree = size//2
            root = [Fraction(0)]*degree + [Fraction(1)]
            for i in reversed(range(degree)):
                root[i] = (f[degree+i]-multiply(root, root)[degree+i])/2
            q = lcm(*(v.denominator for v in root))
            p = [int(q*v) for v in root]
            err = [q*q*c-s for c,s in zip(f, multiply(p,p))]
            while err and not err[-1]:
                err.pop()
            assert err and len(err) <= degree
            if err[-1] < 0:
                err = [-c for c in err]
            # For all n>=start, q² f(n) differs from P(n)² by strictly
            # less than the distance to the immediately preceding square.
            gap = [2*c for c in p]
            gap[0] -= 1
            for i,e in enumerate(err):
                gap[i] -= e
            start = 8
            while not (positive_after(err,start) and positive_after(gap,start)):
                start *= 2
            largest_cutoff = max(largest_cutoff, start)
            for n in range(8,start):
                value = prod(n-i for i in offsets)
                if isqrt(value)**2 == value:
                    exceptions.append((n,offsets))
    assert max(exceptions) == (55,(1,5,6,7))
    print("Even subsets of eight shifts: last exceptional row", max(exceptions),
          "largest polynomial comparison cutoff", largest_cutoff, flush=True)


def represents(a, k):
    lo = hi = 2*k
    while comb(hi, k) < a:
        hi *= 2
    while lo < hi:
        mid = (lo+hi)//2
        if comb(mid, k) < a:
            lo = mid+1
        else:
            hi = mid
    return comb(lo, k) == a


def images(columns, k):
    out = []
    for p in range(11, 1100):
        if any(p % q == 0 for q in range(2, isqrt(p)+1)):
            continue
        common = set.intersection(*({comb(x, col) % p for x in range(p)} for col in columns))
        allowed = tuple(comb(x, k) % p in common for x in range(p))
        out.append((p, allowed))
    return sorted(out, key=lambda item: sum(item[1])/item[0])


def survivors(k, i, j, d, x, y, u, v, end, tests):
    flags = bytearray([1])*end
    # Exact binomial membership has already excluded every row through 64.
    index, xx, yy = 0, x, y
    while index < end and xx+i+j <= 128:
        flags[index] = 0
        xx, yy = u*xx+d*v*yy, v*xx+u*yy
        index += 1
    for p, allowed in tests:
        if flags.find(1) == -1:
            return
        a, b = x % p, y % p
        first = (a, b)
        pattern = []
        while True:
            pattern.append(allowed[(a+i+j)*((p+1)//2) % p])
            a, b = (u*a+d*v*b) % p, (v*a+u*b) % p
            if (a, b) == first:
                break
            assert len(pattern) <= 2*p
        period = len(pattern)
        for r, keep in enumerate(pattern):
            if not keep and r < end:
                flags[r::period] = bytes((end-1-r)//period+1)
    assert flags.find(1) == -1, (k, i, j, d, x, y, flags.find(1))


def verify(columns, k, decade):
    tests = images(columns, k)
    assert all(not all(represents(comb(n,k), col) for col in columns) for n in range(2*k,65))
    # For D=1 the factors of (j-i)^2 give 2x <= 1+(j-i)^2 <= 50.
    assert (25+2*k)//2 < 64
    count = 0
    for d in range(2, 211):
        if 210 % d:
            continue
        # Exhaustive unit and reduced-seed search is tiny for this set of D.
        v = 1
        while (u := isqrt(1+d*v*v))**2 != 1+d*v*v:
            v += 1
        growth = u.bit_length()-1
        end = 2 + (10*decade + 3*factorial(k).bit_length()+6*k)//(3*k*growth)
        assert 3*k*(growth*end-2) >= 10*decade+3*factorial(k).bit_length()
        for i, j in combinations(range(k), 2):
            gap = j-i
            for y in range(v*gap):
                rhs = gap*gap+d*y*y
                x = isqrt(rhs)
                if x*x == rhs:
                    survivors(k, i, j, d, x, y, u, v, end, tests)
                    count += 1
    print(columns, "column", k, "verified", count, "nonsquare-kernel orbits", flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    audit_even_subsets()
    for partner in (3,5,6,7):
        columns = (partner,8)
        for k in columns:
            verify(columns, k, 3209464)
