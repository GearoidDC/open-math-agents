"""Exclude a cap of twenty prime divisors for four proper columns at most seventeen."""

from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import factorial, lcm, prod
from pathlib import Path
import gzip
import json

from Erdos849NineteenLow import occupancies
from Erdos849InterpolatedPowers import DATA, check, endpoint, floor_root, tangent
from Erdos849SingletonInterpolation import branch_bounds


TARGETS = {(7,9):7,(7,10):7,(8,9):8,(8,10):8,(9,10):9,
           **{(j,d):d for j in (8,9,10,11) for d in (16,17)}}
ADDITIONAL = Path(__file__).with_suffix(".json.gz")


@lru_cache(None)
def excluded(k,bounds):
    Q = bounds[0]
    loss = sorted([max(Fraction(1),Fraction(v,Q)) for v in bounds[1:]],reverse=True)
    lower = endpoint(k)-k+1
    cap = lcm(*range(1,k+1))
    coefficients = [max(Fraction(1),Fraction(lower,Q**t)) if k*t<=17 else Fraction(1)
                    for t in range(21)]
    impossible = [value>cap*prod(loss[:t]) for t,value in enumerate(coefficients)]
    E = prod(loss)
    return all(any(impossible[t] for t in counts)
               or prod(coefficients[t] for t in counts)>factorial(k)*E
               for counts in occupancies(k,20))


def verify_pair(j,d,k,base,additional):
    D = lcm(*range(1,d))
    t = 20//k
    Q = 0
    for r in range(j):
        for s in range(d):
            key = f"{j},{d},{r},{s}"
            cert = additional.pop(key,None) or base.get(key,tangent(j,d,r,s))
            h,w,H,_ = check(j,d,r,s,cert)
            assert k*t*w<=j*d*h
            # ceil of the h-th root, valid also when H is a perfect power.
            bound = floor_root(H-1,h)+1
            Q = max(Q,bound)
    L = endpoint(k)-k+1
    M = lcm(*range(1,k+1))
    prime_parts = []
    for p in (2,3,5,7,11,13):
        part = 1
        while D%(p*part)==0:
            part *= p
        prime_parts.append(part)
    assert prod(prime_parts)==D and Q>d
    prime_parts.sort(reverse=True)
    # First exclude fewer than t powers in a slot using its individual cap.
    assert L>M*Q**(t-1)*prod(prime_parts[:t-1])
    if k==7:
        assert t==2 and L>M*Q**2*prod(prime_parts[:2])
    else:
        b = (t+1)*k-20
        assert b>0 and L**b>factorial(k)*D*Q**(t*b)
    return Q


def main():
    with gzip.open(DATA,"rt",encoding="ascii") as handle:
        base = json.load(handle)
    with gzip.open(ADDITIONAL,"rt",encoding="ascii") as handle:
        additional = json.load(handle)
    forbidden = {(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,6),(4,6),(4,8),(7,8)}
    bounds = {(j,d):tuple(max(z) for z in zip(*branch_bounds(j,d,base)))
              for d in range(8,18) for j in range(7,d)}
    residual = []
    for pattern in combinations(range(2,18),4):
        pairs = list(combinations(pattern,2))
        if not forbidden.isdisjoint(pairs):
            continue
        available = [bounds[pair] for pair in pairs if pair in bounds]
        assert available
        best = tuple(min(z) for z in zip(*available))
        if not any(excluded(k,best) for k in pattern):
            residual.append(pattern)
    assert len(residual)==62
    assert all(set(TARGETS).intersection(combinations(pattern,2)) for pattern in residual)
    for (j,d),k in TARGETS.items():
        Q = verify_pair(j,d,k,base,additional)
        print(f"Columns {j},{d}: Q={Q}, excluded using column {k}.")
    assert not additional
    print("Every four-proper-column pattern through column 17 requires at least 21 distinct prime factors above 10^128.")


if __name__=="__main__":
    main()
