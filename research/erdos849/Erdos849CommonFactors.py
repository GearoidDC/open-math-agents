"""Rule out smooth normalized products of proper subsets of three Pascal rows."""

from fractions import Fraction
from itertools import product
from json import loads
from math import factorial
from pathlib import Path

from Erdos849BalancedCuts import lattice, norm_bound, valuation
from Erdos849ComponentMoments import coefficients


PRIMES = (2,3,5,7)
WEIGHTS = (1,2,3,3)
ROOT_LOWER = {3:1, 5:2, 6:2, 7:3}


def prime_exponents(upper):
    # Each p^v_p(a) divides a single term of the seven-term numerator.
    if upper > 2000:
        return dict.fromkeys(PRIMES, upper)
    limit = 5**7 * 10**upper
    out = {}
    for p in PRIMES:
        lo, hi = 0, 1
        while p**(7*hi) <= limit:
            hi *= 2
        while hi > lo+1:
            mid = (lo+hi)//2
            if p**(7*mid) <= limit:
                lo = mid
            else:
                hi = mid
        out[p] = lo
    return out


def vector_length(columns, sizes, lower, scale, caps):
    c = coefficients(columns,sizes)
    powers = [Fraction(v*s,k) for v,s,k in zip(c,sizes,columns)]
    assert all(f.denominator == 1 for f in powers)
    assert sum(map(abs,c)) <= 300
    bounds = []
    for p in PRIMES:
        constant = sum(v*valuation(factorial(k),p) for v,k in zip(powers,columns))
        term_caps = [caps[p]+valuation(factorial(k),p) for k in columns]
        lo = sum(min(0,v)*cap for v,cap in zip(c,term_caps))-constant
        hi = sum(max(0,v)*cap for v,cap in zip(c,term_caps))-constant
        bounds.append(max(-lo,hi))
    factors = [abs(v)*s*(k-s) for v,s,k in zip(c,sizes,columns)]
    assert sum(factors) < 4000
    error = sum(Fraction(f*scale,ROOT_LOWER[k]*10**(lower//k)) for k,f in zip(columns,factors))
    return sum((w*b)**2 for w,b in zip(WEIGHTS,bounds))+(error+Fraction(sum(bounds),2))**2


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    assert 2*30**7*4**5*2**4 < 10**15
    assert 10**22 > 5*(1+25*3)*10**15
    # (k!)^(1/k) > d_k+1/100, and a^(1/k)>100k in the full range.
    for k,d in ROOT_LOWER.items():
        assert factorial(k)*100**k > (100*d+1)**k and 10**128 > (100*k)**k
    assert factorial(7) < 4**7
    cert = loads(Path(__file__).with_name("Erdos849CommonFactors.json").read_text())
    upper = 10**22
    for lower,digits,matrix in cert:
        assert 128 <= lower < upper
        scale = 10**digits
        shortest = norm_bound(lattice(PRIMES,scale,WEIGHTS,matrix))
        caps = prime_exponents(upper)
        for columns in [(3,5,7),(5,6,7)]:
            sizes = product(*(range(1,k) for k in columns))
            longest = max(vector_length(columns,s,lower,scale,caps) for s in sizes)
            assert longest < shortest
            print(columns,lower,upper,"squared length margin exceeds",int(shortest/longest))
        upper = lower
    assert upper == 128


if __name__ == "__main__":
    main()
