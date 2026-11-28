"""Sieve integer-valued rational functions on two pairs involving column seven."""

from fractions import Fraction
from math import comb, factorial, prod
from pathlib import Path
import json
from Erdos849SaturatedCells import integer_valued,missing_denominator,normal_form,roots,slope_bounds
from Erdos849CellSieve import primes,range_sieve


def residue(c,p):
    c=Fraction(c)
    return c.numerator*pow(c.denominator,-1,p)%p


def images(k,i,j,cs,poly,p,control=False):
    a,b=roots(k),roots(7)
    D=missing_denominator(k,7,i,j)
    assert p>max(len(cs),7) and D%p
    ordinary=[(u,v,residue(c,p)) for (u,v),c in poly.items() if v>=0]
    rem=[(u,v,residue(c,p)) for (u,v),c in poly.items() if v<0]
    lhs={}
    for x in (range(p) if k==3 else {n*(n-1)%p for n in range(p)}):
        lhs.setdefault(factorial(7)*prod(x-s for s in a)%p,[]).append(x)
    seen=set()
    for y in range(p):
        m=y+j
        for x in lhs.get(factorial(k)*prod(m-s for s in b)%p,[]):
            if y:
                f=sum(c*pow(x,u,p)*pow(y,v,p) for u,v,c in rem)%p
            elif x==a[i]%p:
                continue
            if control or not y:
                if y:
                    z=D*prod(x-s for s in a if s!=a[i])*pow(factorial(k)*y,-1,p)%p
                else:
                    z=D*prod(m-s for s in b if s!=j)*pow(factorial(7)*(x-a[i]),-1,p)%p
                value=sum(c*comb(z,t) for t,c in enumerate(cs,1) if z>=t)
                value-=sum(c*pow(x,u,p)*pow(y,v,p) for u,v,c in ordinary)
                value%=p
                if y:
                    assert value==f
                f=value
            seen.add(f)
    return seen


def analyze(k,i,j,coefficients,height,limit=397):
    assert k in (3,6) and len(coefficients)>0 and all(type(c)==int for c in coefficients)
    poly=normal_form(k,7,i,j,coefficients)
    integer_valued({key:c for key,c in poly.items() if key[1]>=0},k,7,j)
    rem={key:c for key,c in poly.items() if key[1]<0}
    base,lo,hi=slope_bounds(k,7,height)
    assert rem and all(7*u+3*v<0 for u,v in rem)
    sizes={key:abs(c)*hi**key[0]*Fraction(base)**(7*key[0]+3*key[1]) for key,c in rem.items()}
    size=sum(sizes.values())
    cap=size.numerator//size.denominator
    lead=max(rem,key=lambda key:7*key[0]+3*key[1])
    minimum=abs(rem[lead])*lo**lead[0]*Fraction(base)**(7*lead[0]+3*lead[1])
    sign=0
    if minimum>size-sizes[lead]:
        sign=1 if rem[lead]>0 else -1
    masks=[(p,images(k,i,j,coefficients,poly,p,control=p<53))
           for p in primes(limit) if p>max(len(coefficients),7)]
    survivors=range_sieve(cap,masks)
    if sign:
        survivors=[s for s in survivors if sign*s>0]
    return cap,survivors


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError("Enable assertions.")
    records=json.loads(Path(__file__).with_suffix('.json').read_text())
    assert set(records)=={f'{k},{i},{j}' for k in (3,6) for i in range(3) for j in range(7)}
    for key,record in records.items():
        k,i,j=map(int,key.split(','))
        height,coefficients=record
        assert height==78
        cap,left=analyze(k,i,j,coefficients,height)
        assert not left
        print(key,cap,flush=True)
