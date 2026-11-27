"""Exclude up to nineteen prime factors when the largest proper column is at most 17."""

import gzip
import json
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import factorial, lcm, prod
from pathlib import Path

from Erdos849NineteenLow import occupancies
from Erdos849InterpolatedPowers import check, denominator, expansion, floor_root, tangent
from Erdos849SingletonInterpolation import BASES, DATA, branch_bounds, endpoint


@lru_cache(None)
def excluded(k,constants):
    Q = constants[0]
    ratios = sorted([max(Fraction(1),Fraction(v,Q)) for v in constants[1:]],reverse=True)
    loss = prod(ratios)
    lower = endpoint(k)-k+1
    cap = lcm(*range(1,k+1))
    coefficients = [max(Fraction(1),Fraction(lower,Q**t)) if k*t<=17 else Fraction(1)
                    for t in range(20)]
    impossible = [value>cap*prod(ratios[:t]) for t,value in enumerate(coefficients)]
    return all(any(impossible[t] for t in counts)
               or prod(coefficients[t] for t in counts)>factorial(k)*loss
               for counts in occupancies(k,19))


def fifth_column_bound(j,d,r,s,certificate,T):
    h,w,H,_ = check(j,d,r,s,certificate)
    L = lcm(denominator(d,s),denominator(j,r))
    assert 15*w<j*d*h and H<T**h
    for p in BASES:
        f = 0
        while L%p**(f+1)==0:
            f += 1
        if not f:
            continue
        e0 = 1
        while p**e0<=T:
            e0 += 1
        assert e0>f and p**e0>d
        length = (h*e0+e0-f-1)//(e0-f)
        coefficients = expansion(j,d,r,s,L,certificate[1],length)
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
        assert p**(e0*(j*d*h-15*w))*T**(15*w) >= (H*p**deficit)**(j*d), (j,d,r,s,p)


def main():
    with gzip.open(DATA,"rt",encoding="ascii") as handle:
        data = json.load(handle)
    additional = json.loads(Path(__file__).with_suffix(".json").read_text(encoding="ascii"))
    assert set(additional)=={"9,16,3,13","9,16,5,13","9,16,7,14","9,17,8,0"}
    forbidden = {(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,6),(4,6),(4,8),(7,8)}
    pair_bounds = {(j,d):tuple(max(x) for x in zip(*branch_bounds(j,d,data)))
                   for d in range(8,18) for j in range(7,d)}
    survivors = []
    for pattern in combinations(range(2,18),4):
        pairs = list(combinations(pattern,2))
        if not forbidden.isdisjoint(pairs):
            continue
        available = [pair_bounds[pair] for pair in pairs if pair in pair_bounds]
        assert available
        best = tuple(min(x) for x in zip(*available))
        if not any(excluded(k,best) for k in pattern):
            survivors.append(pattern)
    final_pairs = {(8,17),(9,16),(9,17)}
    assert len(survivors)==8 and all(5 in p and p[-2:] in final_pairs for p in survivors)

    lower = endpoint(5)-4
    T = floor_root(lower//60,3)
    assert T==120013011 and 60*T**3<lower
    count = 0
    for j,d in sorted(final_pairs):
        for r in range(j):
            for s in range(d):
                key = f"{j},{d},{r},{s}"
                certificate = additional.get(key,data.get(key,tangent(j,d,r,s)))
                fifth_column_bound(j,d,r,s,certificate,T)
                count += 1
    print(f"Eight residual patterns include column five. All {count} local branches passed.")
    print("All five-row values >=10^128 with four proper columns at most 17 require at least 20 primes.")


if __name__=="__main__":
    main()
