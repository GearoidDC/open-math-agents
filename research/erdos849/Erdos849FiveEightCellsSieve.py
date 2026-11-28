"""Verify a finite-image sieve for the 20 intersections in columns 8 and 5."""

import json
from fractions import Fraction
from math import comb, factorial, isqrt, prod
from pathlib import Path

from Erdos849SaturatedCells import (
    integer_valued, missing_denominator, normal_form, roots, slope_bounds
)
from Erdos849CellSieve import range_sieve


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def residue(q,p):
    q=Fraction(q)
    return q.numerator*pow(q.denominator,-1,p)%p


def images(i,j,coeffs,poly,p):
    left,right=roots(8),roots(5)
    denom=missing_denominator(8,5,i,j)
    assert p>max(len(coeffs),8) and prime(p) and denom%p
    points={}
    for x in {n*(n-1)%p for n in range(p)}:
        points.setdefault(prod(x-v for v in left)%p,[]).append(x)
    ordinary=[(a,b,residue(c,p)) for (a,b),c in poly.items() if b>=0]
    rem=[(a,b,residue(c,p)) for (a,b),c in poly.items() if b<0]
    seen=set()
    for m in range(p):
        y=(m-j)%p
        for x in points.get(336*prod(m-v for v in right)%p,[]):
            if y:
                seen.add(sum(c*pow(x,a,p)*pow(y,b,p) for a,b,c in rem)%p)
            elif x!=left[i]%p:
                z=(denom*prod(m-v for v in right if v!=j)*pow(120*(x-left[i]),-1,p))%p
                value=sum(c*comb(z,d) for d,c in enumerate(coeffs,1) if z>=d)
                value-=sum(c*pow(x,a,p) for a,b,c in ordinary if not b)
                seen.add(value%p)
    return seen


def direct_image(i,j,coeffs,poly,p):
    left,right=roots(8),roots(5)
    denom=missing_denominator(8,5,i,j)
    ordinary=[(a,b,residue(c,p)) for (a,b),c in poly.items() if b>=0]
    seen=set()
    for x in {n*(n-1)%p for n in range(p)}:
        for m in range(p):
            y=(m-j)%p
            if (prod(x-v for v in left)-336*prod(m-v for v in right))%p:
                continue
            lhs=denom*prod(x-v for v in left if v!=left[i])
            rhs=denom*prod(m-v for v in right if v!=j)
            regular=sum(c*pow(x,a,p)*pow(y,b,p) for a,b,c in ordinary)%p
            for z in range(p):
                if (factorial(8)*y*z-lhs)%p or (120*(x-left[i])*z-rhs)%p:
                    continue
                value=sum(c*comb(z,d) for d,c in enumerate(coeffs,1) if z>=d)
                seen.add((value-regular)%p)
    return seen


def radius(k,h,coeffs,poly,height):
    base,lo,hi=slope_bounds(k,h,height)
    u,v=len(roots(k)),len(roots(h))
    rem={xy:c for xy,c in poly.items() if xy[1]<0}
    assert rem and all(v*i+u*j<0 for i,j in rem)
    upper=sum(abs(c)*hi**i*Fraction(base)**(v*i+u*j) for (i,j),c in rem.items())
    return upper.numerator//upper.denominator


def solve_cell(i,j,coeffs,limit=139):
    assert coeffs and all(type(c)==int for c in coeffs)
    poly=normal_form(8,5,i,j,coeffs)
    integer_valued({xy:c for xy,c in poly.items() if xy[1]>=0},8,5,j)
    cap=radius(8,5,coeffs,poly,90)
    masks=[(p,images(i,j,coeffs,poly,p)) for p in range(max(9,len(coeffs)+1),limit+1) if prime(p)]
    for p,good in masks[:2]:
        assert good==direct_image(i,j,coeffs,poly,p)
    small=min(cap,1000)
    direct=[v for v in range(-small,small+1) if all(v%p in ids for p,ids in masks[:3])]
    assert range_sieve(small,masks[:3])==direct
    return cap,range_sieve(cap,masks)


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError("Enable assertions.")
    data=json.loads(Path(__file__).with_suffix('.json').read_text())
    assert set(data)=={f'{i},{j}' for i in range(4) for j in range(5)}
    for key,coeffs in data.items():
        i,j=map(int,key.split(','))
        cap,left=solve_cell(i,j,coeffs)
        print(i,j,cap,left,flush=True)
        assert not left
