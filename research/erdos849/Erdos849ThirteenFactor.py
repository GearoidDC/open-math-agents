"""Verify the factor 13 on the remaining intervals for forty-prime five-row candidates."""

import gzip
import json
from functools import cache
from itertools import product
from math import factorial, prod
from pathlib import Path

from Erdos849LocalInterpolation import floor_root
from Erdos849RawCellTools import derivative, falling
from Erdos849ResidueDisks import fibers


@cache
def size_bounds(cols,lo,hi,exponents):
    # A reflected even coordinate is k-1-n, whose absolute value is n-k+1.
    low=[floor_root(factorial(k)*lo,k)-k for k in cols]
    high=[floor_root(factorial(k)*hi,k)+k for k in cols]
    assert min(low)>0
    return [(prod(x**e for x,e in zip(low,es)),prod(x**e for x,e in zip(high,es)))
            for es in exponents]


def real_exclusion(cols,low,high,exponents,polys):
    pieces=[]
    for flip in product(*[(1,-1) if k%2==0 else (1,) for k in cols]):
        signs=[prod(s**e for s,e in zip(flip,es)) for es in exponents]
        signed=[[c*s for c,s in zip(cs,signs)] for cs in polys]
        pending=[(10**low,10**high)];n=0
        while pending:
            lo,hi=pending.pop()
            bounds=size_bounds(cols,lo,hi,exponents)
            for cs in signed:
                bot=sum(c*(u if c>=0 else v) for c,(u,v) in zip(cs,bounds))
                top=sum(c*(v if c>=0 else u) for c,(u,v) in zip(cs,bounds))
                if bot>0 or top<0:break
            else:
                assert lo<hi
                mid=floor_root(lo*hi,2)
                assert lo<=mid<hi
                pending.extend([(lo,mid),(mid+1,hi)])
                continue
            n+=1
        pieces.append(n)
    return pieces


def verify_disk(record):
    cols=tuple(record["cols"]);H=record["height"];low=record["low"]
    d=record["d"];A=record["A"];E=record["N"]
    assert (cols,low,H) in (((8,7,6,5),146,170),((8,7,5,3),137,185))
    assert E>0 and d in (2,3) and 0<=A<13**d and A%13==1
    degrees=tuple(tuple(v) for v in record["exponents"]);polys=record["polys"]
    assert polys and all(len(cs)==len(degrees) and all(type(c) is int for c in cs) for cs in polys)
    assert all(len(es)==len(cols) and all(type(e) is int and 0<=e<k for e,k in zip(es,cols)) for es in degrees)
    b=13**d;Q=b**E
    hi=[floor_root(factorial(k)*10**H,k)+k for k in cols]
    weights=[prod(x**e for x,e in zip(hi,es)) for es in degrees]
    assert all(sum(abs(c)*w for c,w in zip(cs,weights))<Q for cs in polys)
    gamma=fibers(cols,13,True)
    assert set(gamma)=={0,1} and gamma[1]==[cols]
    for t in range(E):
        a=A+b*t
        powers=[]
        for k in cols:
            n=k;digits=1
            assert derivative(n,k)%13
            while digits<d*E:
                digits=min(2*digits,d*E);q=13**digits
                n=(n-(falling(n,k)-factorial(k)*a)*pow(derivative(n,k),-1,q))%q
            assert n%13==k and (falling(n,k)-factorial(k)*a)%Q==0
            powers.append([pow(n,e,Q) for e in range(k)])
        vals=[prod(v[e] for v,e in zip(powers,es))%Q for es in degrees]
        assert all(sum(c*x for c,x in zip(cs,vals))%Q==0 for cs in polys)
    return real_exclusion(cols,low,H,degrees,polys)


def verify(records, cols):
    modulus=13**max(r["d"] for r in records)
    assert modulus in (169,2197)
    assert all(sum(t%(13**r["d"])==r["A"] for r in records)==1
               for t in range(1,modulus,13))
    assert all(tuple(r["cols"])==cols for r in records)
    return [verify_disk(r) for r in records]


if __name__=="__main__":
    if not __debug__:raise RuntimeError("Enable assertions to verify the certificates")
    data=json.loads(gzip.decompress(Path(__file__).with_suffix(".json.gz").read_bytes()))
    assert len(data)==2 and {tuple(pattern[0]["cols"]) for pattern in data}=={(8,7,5,3),(8,7,6,5)}
    for pattern in data:
        cols=tuple(pattern[0]["cols"])
        pieces=verify(pattern,cols)
        print(cols, len(pieces), sum(sum(s) for s in pieces))
