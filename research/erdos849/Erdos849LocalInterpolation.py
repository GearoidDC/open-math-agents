"""Verify local interpolation certificates for common binomial columns 7 and 8.

Run with Python 3.8 or newer. All acceptance conditions use integer arithmetic.
"""

import json
from math import comb, factorial, prod
from pathlib import Path


HEIGHT = 10**128
DENOMINATOR = 420
DATA = Path(__file__).with_suffix(".json")


def floor_root(value, degree):
    lo, hi = 0, 1 << ((value.bit_length()+degree-1)//degree)
    while lo+1 < hi:
        mid = (lo+hi)//2
        if mid**degree <= value:
            lo = mid
        else:
            hi = mid
    assert lo**degree <= value < (lo+1)**degree
    return lo


def multiply(left, right):
    """Multiply in the truncated power series ring Z[z]/z^h."""
    return [sum(left[i]*right[d-i] for i in range(d+1)) for d in range(len(left))]


def shifted_row(k, s, h):
    """Solve u*product(1+D_v*u)=z, return the shifted row x=c*420*u."""
    c = factorial(k)//prod(s-v for v in range(k) if v!=s)
    scale = DENOMINATOR*c
    factors = [scale//(s-v) for v in range(k) if v!=s]
    assert all(scale%(s-v)==0 for v in range(k) if v!=s)
    u = [0]*h
    # Iterate the inverse equation one coefficient at a time. The nonlinear
    # terms have no dependence on u[t] in coefficient t since u[0]=0.
    def equation():
        result = u.copy()
        for factor in factors:
            result = multiply(result,[1]+[factor*b for b in u[1:]])
        return result

    for t in range(1,h):
        u[t] = int(t==1)-equation()[t]
    assert equation() == [0,1]+[0]*(h-2)
    return [scale*b for b in u]


def powers(row, k):
    result = [[1]+[0]*(len(row)-1)]
    for _ in range(k):
        result.append(multiply(result[-1],row))
    return result


def verify(s, r, certificate):
    weight_limit, h, coefficients = certificate
    assert 2 <= h and 0 < weight_limit < 56
    monomials = sorted((7*i+8*j,i,j) for i in range(8) for j in range(7)
                       if 0 < 7*i+8*j <= weight_limit)
    assert len(monomials)==len(coefficients)
    terms = [(c,w,i,j) for c,(w,i,j) in zip(coefficients,monomials) if c]
    largest_weight = max(w for _,w,_,_ in terms)
    assert largest_weight*16 <= 56*h
    assert 196*largest_weight <= 11*56*h
    xs = powers(shifted_row(8,s,h),7)
    ys = powers(shifted_row(7,r,h),6)
    expansion = [0]*h
    for c,_,i,j in terms:
        term = multiply(xs[i],ys[j])
        expansion = [a+c*b for a,b in zip(expansion,term)]
    assert expansion == [0]*h, (s,r,"order of vanishing")

    roots = [floor_root(factorial(k)*HEIGHT,k) for k in (8,7)]
    lower = roots[0]-s, roots[1]-r
    upper = roots[0]+8-s, roots[1]+7-r
    assert min(lower)>0
    # Choose the eventual sign, then certify the same sign for every t>=1.
    # After t=1+u the polynomial lower bound has nonnegative coefficients
    # and its constant coefficient is positive.
    sign = 1 if terms[-1][0]>0 else -1
    positive_bound = []
    for c,w,i,j in terms:
        endpoints = lower if c*sign>0 else upper
        positive_bound.append((w,c*sign*endpoints[0]**i*endpoints[1]**j))
    translated = [sum(b*comb(w,t) for w,b in positive_bound if t<=w)
                  for t in range(largest_weight+1)]
    assert translated[0]>0 and min(translated)>=0, (s,r,"nonzero value")
    absolute_bound = max(sum(abs(c)*upper[0]**i*upper[1]**j for c,_,i,j in terms
                             if c*side>0) for side in (-1,1))
    return floor_root(absolute_bound,h)+1


def main():
    data = json.loads(DATA.read_text(encoding="ascii"))
    assert set(data)=={f"{s},{r}" for s in range(8) for r in range(7)}
    Q = max(verify(s,r,data[f"{s},{r}"]) for s in range(8) for r in range(7))
    assert DENOMINATOR*Q**16 < HEIGHT
    assert (DENOMINATOR*Q**17)**196 * 10**((238-128)*17*11) < 10**(238*196)
    print(f"Verified 56 branches, Q={Q}, and 420*Q^16 < 10^128.")
    print("Every common value of columns 7 and 8 at least 10^128 has at least 17 prime divisors.")
    print("The same certificates force 18 distinct prime divisors above 10^238.")


if __name__=="__main__":
    main()
