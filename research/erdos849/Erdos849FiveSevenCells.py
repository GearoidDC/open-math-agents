"""Check occupied assignments in columns five and seven above a stated height."""

from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json

from Erdos849CellSieve import primes, range_sieve
from Erdos849SaturatedCells import integer_valued, missing_denominator, normal_form, slope_bounds


def images(i,j,p,coefficients,remainder,ordinary,denominator,extras):
    def image(k):
        return [comb(x,k)%p if x>=k else 0 for x in range(p)]
    common=set(range(p))
    for k in extras:
        common.intersection_update(image(k))
    by_value={}
    for x,value in enumerate(image(5)):
        if value in common:
            by_value.setdefault(value,[]).append(x)
    def reduction(poly):
        return [(u,v,c.numerator*pow(c.denominator,-1,p)%p) for (u,v),c in poly.items()]
    terms=reduction(remainder)
    regs=reduction(ordinary)
    values=set()
    for m,value in enumerate(image(7)):
        y=(m-j)%p
        for x in by_value.get(value,[]):
            if y:
                f=sum(c*pow(x,u,p)*pow(y,v,p) for u,v,c in terms)%p
            elif x!=i:
                z=denominator*factorial(j)*factorial(6-j)*(-1)**(6-j)*pow(factorial(7)*(x-i),-1,p)%p
                f=(sum(c*comb(z,t) for t,c in enumerate(coefficients,1) if t<=z)
                   -sum(c*pow(x,u,p)*pow(y,v,p) for u,v,c in regs))%p
            else:
                # Z*(x-i) would equal a nonzero derivative modulo this good prime.
                continue
            values.add(f)
    return values


def analyze(i,j,cs,height,extras=(),prime_limit=281,max_cap=None):
    assert 0<=i<5 and 0<=j<7 and cs and all(type(c)==int for c in cs)
    poly=normal_form(5,7,i,j,cs)
    ordinary={key:c for key,c in poly.items() if key[1]>=0}
    integer_valued(ordinary,5,7,j)
    rem={key:c for key,c in poly.items() if key[1]<0}
    base,lo,hi=slope_bounds(5,7,height)
    weight=lambda key:7*key[0]+5*key[1]
    lead=max(rem,key=weight)
    assert weight(lead)<0
    sizes={key:abs(c)*hi**key[0]*Fraction(base)**weight(key) for key,c in rem.items()}
    total=sum(sizes.values())
    cap=total.numerator//total.denominator
    lower=abs(rem[lead])*lo**lead[0]*Fraction(base)**weight(lead)
    sign=(1 if rem[lead]>0 else -1) if lower>total-sizes[lead] else 0
    if cap==0 and sign:
        return cap,[]
    if max_cap is not None and cap>max_cap:
        return cap,None
    d=missing_denominator(5,7,i,j)
    rules=[(p,images(i,j,p,cs,rem,ordinary,d,extras)) for p in primes(prime_limit) if p>max(len(cs),7)]
    survivors=range_sieve(cap,rules)
    return cap,[f for f in survivors if sign==0 or f*sign>0]


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Enable assertions.')
    data=json.loads(Path(__file__).with_suffix('.json').read_text())
    assert set(data)=={f'{i},{j}' for i in range(5) for j in range(7)}
    for key,(height,cs) in sorted(data.items()):
        i,j=map(int,key.split(','))
        assert height<=400
        bound,left=analyze(i,j,cs,height)
        assert left==[]
        print(key,height,bound,flush=True)
