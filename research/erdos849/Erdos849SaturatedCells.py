"""Check integral-function certificates for occupied Pascal prime assignments."""

import json
from fractions import Fraction
from functools import cache
from math import factorial, gcd, lcm
from pathlib import Path

from Erdos849CellSieve import row_states, valuation


def roots(k):
    if k % 2:
        return tuple(range(k))
    return tuple(i*(i+1) for i in range(k//2))


def positions(k, i):
    if k % 2:
        return (i,)
    return (k//2-1-i, k//2+i)


@cache
def missing_denominator(k, h, i, j):
    denominator = 1
    for prime in (2, 3, 5, 7):
        if prime > max(k, h):
            break
        limit = 3+max(valuation(factorial(n),prime) for n in (k,h))
        left = row_states(k, positions(k,i), prime, limit)
        right = row_states(h, positions(h,j), prime, limit)
        cost = max(x+y-e for e in range(limit+1) for x,f in left[e]
                   for y,g in right[e] if not (f and g))
        denominator *= prime**max(0,cost)
    return denominator


def add(out, term, coefficient, offset_x=0, offset_y=0):
    for (i,j), c in term.items():
        key = i+offset_x,j+offset_y
        result = out.get(key,0)+coefficient*c
        if result:
            out[key] = result
        else:
            out.pop(key,None)


def multiply(left, right):
    out = {}
    for (i,j), c in left.items():
        add(out,right,c,i,j)
    return out


def product_polynomial(offsets, shift, variable):
    out = {(0,0):1}
    for s in offsets:
        out = multiply(out,{variable:1,(0,0):shift-s})
    return out


def normal_form(k,h,i,j,coefficients):
    left, right = roots(k), roots(h)
    u = len(left)
    lhs = product_polynomial(left,0,(1,0))
    del lhs[u,0]
    relation = {}
    add(relation,lhs,-1)
    add(relation,product_polynomial(right,right[j],(0,1)),Fraction(factorial(k),factorial(h)))
    z = {}
    other = left[:i]+left[i+1:]
    add(z,product_polynomial(other,0,(1,0)),
        Fraction(missing_denominator(k,h,i,j),factorial(k)),offset_y=-1)
    result = {}
    power = {(0,0):1}
    for d, coefficient in enumerate(coefficients,1):
        # Construct binom(Z,d) from binom(Z,d-1).
        expanded = multiply(power,z)
        add(expanded,power,1-d)
        for n in range(2*u-2,u-1,-1):
            for key in [key for key in expanded if key[0]==n]:
                add(expanded,relation,expanded.pop(key),n-u,key[1])
        power = {key:Fraction(val,d) for key,val in expanded.items()}
        add(result,power,coefficient)
    return result


def floor_root(n,d):
    lo,hi=0,1<<((n.bit_length()+d-1)//d)
    while hi-lo>1:
        mid=(hi+lo)//2
        if mid**d<=n:
            lo=mid
        else:
            hi=mid
    return lo


@cache
def slope_bounds(k,h,height):
    a,b=roots(k),roots(h)
    u,v=len(a),len(b)
    assert gcd(u,v)==1 and min(a)==min(b)==0
    base=floor_root(factorial(h)*10**height,u*v)-1
    y=base**u
    assert base>=1 and (y+max(b))**v < factorial(h)*10**height
    ratio=Fraction(factorial(k),factorial(h))
    den=10**6
    n=floor_root(den**u*ratio.numerator//ratio.denominator,u)
    low,high=Fraction(n-1,den), Fraction(n+2,den)
    assert low>0 and low**u < ratio*Fraction(y-max(b),y)**v
    upper_base=high-Fraction(max(a),base**v)
    assert upper_base>0 and upper_base**u > ratio*Fraction(y+max(b),y)**v
    return base,low,high


def integer_valued(poly,k,h,shift):
    if not poly:
        return
    den=lcm(*(Fraction(v).denominator for v in poly.values()))
    dx=max(i for i,j in poly)
    dy=max(j for i,j in poly)
    for n in range(1+dx*(1+int(k%2==0))):
        x=n if k%2 else n*(n-1)
        cols=[0]*(dy+1)
        for (i,j),v in poly.items():
            cols[j]+=int(v*den)*x**i
        for m in range(1+dy*(1+int(h%2==0))):
            y=m-shift if h%2 else m*(m-1)-shift
            val=0
            for c in reversed(cols):
                val=(val*y+c)%den
            assert val==0


def check(k,h,i,j,height,coefficients):
    assert all(type(c) is int for c in coefficients)
    u,v=len(roots(k)),len(roots(h))
    base,low,high=slope_bounds(k,h,height)
    poly=normal_form(k,h,i,j,coefficients)
    integer_valued({key:c for key,c in poly.items() if key[1]>=0},k,h,roots(h)[j])
    rem={key:c for key,c in poly.items() if key[1]<0}
    assert rem
    def weight(key):
        return v*key[0]+u*key[1]
    lead=max(rem,key=weight)
    assert weight(lead)<0
    bounds={key:abs(c)*high**key[0]*Fraction(base)**weight(key) for key,c in rem.items()}
    assert sum(bounds.values())<1
    lower=abs(rem[lead])*low**lead[0]*Fraction(base)**weight(lead)
    assert lower>sum(val for key,val in bounds.items() if key!=lead)


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    records=json.loads(Path(__file__).with_suffix('.json').read_text())
    for k,h,height,data in records:
        assert len(data)==len(roots(k)) and all(len(row)==len(roots(h)) for row in data)
        for i,row in enumerate(data):
            for j,coeffs in enumerate(row):
                check(k,h,i,j,height,coeffs)
        print(k,h,height,len(roots(k))*len(roots(h)),"occupied cells",flush=True)


if __name__=='__main__':
    main()
