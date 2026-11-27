"""Prove that common values of columns 7 and 8 above 10^128 need 24 prime bases."""

import gzip
import json
from itertools import combinations_with_replacement
from math import comb, gcd, lcm
from pathlib import Path

from Erdos849InterpolatedPowers import check, denominator, endpoint, expansion, floor_root


BASES = (2,3,5,7)
COFACTOR = lcm(*range(1,9))
DATA = Path(__file__).with_suffix(".json.gz")


def refined(terms,s,r,L,h,H,ordinary,p):
    """Use the known valuation of a large p-power to recover denominator loss."""
    f = 0
    while L%p**(f+1)==0:
        f += 1
    if f==0:
        return ordinary
    e = 1
    while p**e<ordinary:
        e += 1
    bounds = []
    for e0 in (e-1,e,e+1):
        assert e0>f and p**e0>8
        length = (h*e0+e0-f-1)//(e0-f)
        coefficients = expansion(7,8,r,s,L,terms,length)
        assert not any(coefficients[:h])
        deficit = 0
        for t in range(h,length):
            c = coefficients[t]
            if c:
                v = 0
                while c%p==0:
                    c //= p
                    v += 1
                deficit = max(deficit,h*e0-t*(e0-f)-v)
        bounds.append(max(p**(e0-1),floor_root(H*p**deficit,h)+1))
    return min(bounds)


def main():
    with gzip.open(DATA,"rt",encoding="ascii") as f:
        data = json.load(f)
    assert len(data)==56
    peak = 0
    for s in range(8):
        bounds = [0]*5
        for r in range(7):
            certificate = data[f"7,8,{r},{s}"]
            h,w,H,_ = check(7,8,r,s,certificate)
            assert 19*w<=56*h
            ordinary = floor_root(H,h)+1
            assert ordinary>8
            L = lcm(denominator(8,s),denominator(7,r))
            row = [ordinary]+[refined(certificate[1],s,r,L,h,H,ordinary,p) for p in BASES]
            bounds = [max(a,b) for a,b in zip(bounds,row)]
        # Two bases can be ordinary, and two exceptional bases must differ.
        # Trivial padding by 1 also covers slots with zero or one power.
        for i,j in combinations_with_replacement(range(5),2):
            if i!=0 and i==j:
                continue
            cap = COFACTOR
            for index in (i,j):
                if index==0:
                    continue
                p = BASES[index-1]
                part = 1
                while COFACTOR%(p*part)==0:
                    part *= p
                cap = cap//part*gcd(part,8*comb(7,s))
            assert cap*bounds[i]*bounds[j]<endpoint(8)-s, (s,i,j)
        peak = max(peak,bounds[0])
    print(f"Verified 56 branch polynomials; ordinary Q <= {peak}.")
    print("Every one of the eight numerator terms hosts at least three distinct prime powers.")
    print("At least 24 distinct prime factors for C(n,8)=C(m,7) >= 10^128.")


if __name__=="__main__":
    main()
