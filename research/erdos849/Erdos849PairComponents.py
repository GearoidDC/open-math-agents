"""Check the two-row component bound by exact moments and logarithm lattices."""

from collections import defaultdict
from functools import cache
from fractions import Fraction
from itertools import combinations, product
from json import loads
from math import factorial, gcd
from pathlib import Path

from Erdos849BalancedCuts import lattice, norm_bound, valuation
from Erdos849ComponentMoments import floor_root


PAIRS = ((3, 5), (3, 7), (3, 8), (5, 6), (5, 7), (5, 8),
         (6, 7), (6, 8), (7, 8))
PRIMES = (2, 3, 5, 7)
WEIGHTS = (1, 2, 3, 3)
LOW_TRANSFORM = [
    [-29982, -1974, 5533, 7218],
    [30345, -30950, 12223, -3445],
    [31871, -171, -5395, -6794],
    [29349, -17965, -15813, 12767],
]


def compositions(n):
    return [(i, j, n-i-j) for i in range(n+1) for j in range(n-i+1)]


def kernels(k, h):
    for u, v in product(compositions(k), compositions(h)):
        if any(a+b == 0 for a, b in zip(u, v)):
            continue
        if list(zip(u, v)) != sorted(zip(u, v)):
            continue
        c = [u[(i+1)%3]*v[(i+2)%3]-u[(i+2)%3]*v[(i+1)%3] for i in range(3)]
        if not any(c):
            i, j = next((i,j) for i,j in combinations(range(3), 2) if u[i]*u[j])
            c[i], c[j] = u[j], -u[i]
        common = gcd(*c)
        c = tuple(x//common for x in c)
        assert all(sum(x*y for x,y in zip(c,row)) == 0 for row in (u,v))
        yield u, v, c


@cache
def profiles(k, counts, weights):
    """First nonzero integer moment for each distinct arrangement of a row."""
    coeffs = tuple(sorted(w for n,w in zip(counts, weights) for _ in range(n)))
    if not any(coeffs):
        return {}
    return moments(coeffs)


@cache
def moments(coeffs):
    n = len(coeffs)
    by_order = defaultdict(set)
    groups = sorted(set(coeffs))
    offsets = tuple(range(n-1, -n, -2))
    def divide(remaining, j, values):
        if j == len(groups)-1:
            full = values + [(x, groups[j]) for x in remaining]
            for order in range(1, n):
                m = sum(w*x**order for x,w in full)
                if m:
                    by_order[order].add(m)
                    return
            raise AssertionError("Vandermonde kernel")
        for chosen in combinations(remaining, coeffs.count(groups[j])):
            divide(tuple(x for x in remaining if x not in chosen), j+1,
                   values+[(x,groups[j]) for x in chosen])
    divide(offsets, 0, [])
    return dict(by_order)


@cache
def scale_bounds(k, threshold, order, total):
    # After normalization by (a/10^threshold)^(order/k), the absolute
    # moment contributes between lo and hi per unit. The rest costs err.
    z = floor_root(factorial(k)*10**threshold, k)
    dmin, dmax = 2*z-k, 2*(z+1)+k
    lo, hi = Fraction(1,order*dmax**order), Fraction(1,order*dmin**order)
    err = Fraction(2*total*(k-1)**(order+1), (order+1)*dmin**(order+1))
    return lo, hi, err


def check_moments(k, h, u, v, c, threshold):
    rows = []
    for n, counts in ((k,u),(h,v)):
        total = sum(i*abs(j) for i,j in zip(counts,c))
        p = profiles(n,counts,c)
        profile = {}
        for r, values in p.items():
            lo, hi, err = scale_bounds(n,threshold,r,total)
            lower = min(map(abs, values))*lo-err
            upper = max(map(abs, values))*hi+err
            assert lower > 0
            profile[r] = (lower,upper,values,lo,hi,err)
        rows.append(profile)
    assert any(rows)
    for r,s in product(*rows):
        left,right = rows[0][r],rows[1][s]
        if r*h != s*k:
            slow,fast = (left,right) if r*h < s*k else (right,left)
            assert slow[0] > fast[1], (k,h,u,v,c,r,s,float(slow[0]/fast[1]))
        else:
            for x,y in product(set(map(abs,left[2])),set(map(abs,right[2]))):
                assert (x*left[3]-left[5] > y*right[4]+right[5]
                        or y*right[3]-right[5] > x*left[4]+left[5])


def impossible_sizes(k,h,u,v,threshold):
    for small,large in zip(u,v):
        gap = Fraction(large-4,h)-Fraction(small,k)
        if gap > 0 and 10**(threshold*gap.numerator) > (factorial(h)*9**(4+small))**gap.denominator:
            return True
    return False


@cache
def exponent_cap(h,p,upper):
    if upper > 2000:
        return upper
    cap = 9**h * 10**upper
    lo, hi = 0, 1+cap.bit_length()//h
    while hi-lo > 1:
        mid = (lo+hi)//2
        if p**(h*mid) <= cap:
            lo = mid
        else:
            hi = mid
    return lo


@cache
def denominator(d,lower):
    return 2*floor_root(factorial(d)*10**lower,d)-2*d


def spread(counts,c):
    ordered = sorted(x for n,x in zip(counts,c) for _ in range(n))
    return 2*sum(i*x for i,x in enumerate(ordered))


def lattice_check(k,h,shapes,threshold):
    cert = loads(Path(__file__).with_name("Erdos849CommonFactors.json").read_text())
    upper = 10**22
    for lower,digits,matrix in cert:
        if lower == 128:
            digits,matrix = 18,LOW_TRANSFORM
        lower = max(threshold,lower)
        if lower >= upper:
            break
        scale = 10**digits
        shortest = norm_bound(lattice(PRIMES,scale,WEIGHTS,matrix))
        for u,v,c in shapes:
            err = sum(Fraction(spread(counts,c)*scale,
                               denominator(d,lower))
                      for d,counts in ((k,u),(h,v)))
            bounds = []
            for p in PRIMES:
                # p^e divides a term in the longer row. n_h < 9 a^(1/h).
                ep = exponent_cap(h,p,upper)
                # At p>7 equal component weights cancel. At small p each
                # side is between the smallest/largest weight times its
                # total valuation ep + v_p(d!).
                limits = []
                for d,counts in ((k,u),(h,v)):
                    present = [w for n,w in zip(counts,c) if n]
                    limits.append((min(present)*(ep+valuation(factorial(d),p)),
                                   max(present)*(ep+valuation(factorial(d),p))))
                bounds.append(max(limits[0][1]-limits[1][0],limits[1][1]-limits[0][0]))
            length = sum((b*w)**2 for b,w in zip(bounds,WEIGHTS))+(err+Fraction(sum(bounds),2))**2
            assert length < shortest, (k,h,u,v,lower,float(shortest/length))
        upper = lower
    assert upper == threshold


def main():
    if not __debug__:
        raise RuntimeError("Assertions must be enabled")
    for k,h in PAIRS:
        shapes = list(kernels(k,h))
        threshold = 128
        # For t>=10^22, |b_p|<1000t and log|W-1|<-t/5. Matveev's
        # four-logarithm constant is less than 10^15.
        assert factorial(h) < 5**h and 2**h < 10**(h-1)
        assert factorial(k)*2**k > 3**k and factorial(h)*2**h > 3**h
        assert 2*30**7*4**5*2**4 < 10**15 < 10**22//(5*(1+25*3))
        for u,v,c in shapes:
            if not impossible_sizes(k,h,u,v,threshold):
                check_moments(k,h,u,v,c,threshold)
            assert max(map(abs,c)) <= 56
        lattice_check(k,h,shapes,threshold)
        print(k,h,threshold,len(shapes),flush=True)


if __name__ == "__main__":
    main()
