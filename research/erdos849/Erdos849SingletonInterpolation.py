"""Check the interpolation and cofactor obstruction for columns 15, 16 and 17."""

import gzip
import json
from fractions import Fraction
from math import factorial, lcm, prod

from Erdos849InterpolatedPowers import (
    DATA, check, denominator, endpoint, expansion, floor_root, tangent,
)


BASES = (2,3,5,7,11,13)


def prime_bound(j,d,r,s,L,h,H,terms,p):
    """Constant Q_p in P <= Q_p*(a/10^128)^(1/17)."""
    f, pf = 0, 1
    while L%(pf*p)==0:
        pf *= p
        f += 1
    ordinary = floor_root(H,h)+1
    assert ordinary>d
    if f==0:
        return ordinary
    e0 = 1
    while p**e0<=10**7:
        e0 += 1
    assert e0>f and p**e0>d
    length = (h*e0+e0-f-1)//(e0-f)
    coefficients = expansion(j,d,r,s,L,terms,length)
    assert not any(coefficients[:h])
    deficit = 0
    for t in range(h,length):
        value = coefficients[t]
        if value:
            v = 0
            while value%p==0:
                value //= p
                v += 1
            deficit = max(deficit,h*e0-t*(e0-f)-v)
    return max(p**(e0-1),floor_root(H*p**deficit,h)+1)


def branch_bounds(j,d,data):
    bounds = []
    for s in range(d):
        maximum = [0]*(len(BASES)+1)
        for r in range(j):
            certificate = data.get(f"{j},{d},{r},{s}",tangent(j,d,r,s))
            h,w,H,_ = check(j,d,r,s,certificate)
            assert 17*w<=j*d*h
            L = lcm(denominator(d,s),denominator(j,r))
            ordinary = floor_root(H,h)+1
            q = [ordinary]+[prime_bound(j,d,r,s,L,h,H,certificate[1],p) for p in BASES]
            maximum = [max(a,b) for a,b in zip(maximum,q)]
        bounds.append(maximum)
    return bounds


def cofactor_bounds(d,bounds):
    """Conservative product lower bounds indexed by the number of empty slots."""
    exceptional = prod(max(Fraction(1),max(Fraction(row[i],row[0]) for row in bounds))
                      for i in range(1,len(BASES)+1))
    empty = sorted(endpoint(d)-s for s in range(d))
    single = sorted(Fraction(endpoint(d)-s,row[0]) for s,row in enumerate(bounds))
    assert min(single)>1
    return [Fraction(prod(empty[:e])*prod(single[:max(0,2*d-17-2*e)]),exceptional)
            for e in range(d+1)]


def main():
    with gzip.open(DATA,"rt",encoding="ascii") as handle:
        data = json.load(handle)
    for d in (15,16,17):
        excluded,nonempty = [],[]
        for j in range(7,d):
            bounds = cofactor_bounds(d,branch_bounds(j,d,data))
            if min(bounds)>factorial(d):
                excluded.append(j)
            elif min(bounds[1:])>factorial(d):
                nonempty.append(j)
        assert excluded==list(range(7,d)) if d<17 else excluded==list(range(12,17))
        assert nonempty==([] if d<17 else list(range(7,12)))
        print(f"d={d}: excluded j={excluded}, remaining all-singleton j={nonempty}")


if __name__=="__main__":
    main()
