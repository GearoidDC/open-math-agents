"""Integer verifier for full prime powers in common binomial values."""

import gzip
import json
from functools import lru_cache
from math import comb, factorial, gcd, lcm, prod
from pathlib import Path

from Erdos849LocalInterpolation import floor_root, multiply, powers


HEIGHT = 10**128
FIRST_DEEP_COLUMN = 18
DATA = Path(__file__).with_suffix(".json.gz")


def weight(k, s):
    return factorial(k)//prod(s-v for v in range(k) if s != v)


def denominator(k, s):
    c = weight(k,s)
    return lcm(*(abs(s-v)//gcd(c,s-v) for v in range(k) if v != s))


@lru_cache(None)
def row_powers(k, s, L, h):
    """Generate the powers of the shifted row x=L*c*u modulo z^h."""
    scale = L*weight(k,s)
    multipliers = [scale//(s-v) for v in range(k) if v != s]
    assert all(scale%(s-v)==0 for v in range(k) if v != s)
    # Write the branch equation as u*g(u)=z. Its coefficient of u is 1.
    g = [1]
    for b in multipliers:
        g = [a+b*c for a,c in zip(g+[0],[0]+g)]
    u = [0]*h
    us = [[0]*h for _ in range(k+1)]
    for t in range(1,h):
        for i in range(2,min(k,t)+1):
            us[i][t] = sum(u[q]*us[i-1][t-q] for q in range(1,t))
        u[t] = int(t==1)-sum(g[i-1]*us[i][t] for i in range(2,k+1))
        us[1][t] = u[t]
    return powers([v*scale for v in u],k-1)


@lru_cache(None)
def endpoint(k):
    return floor_root(factorial(k)*HEIGHT,k)


def tangent(j,d,r,s):
    """The normalized linear polynomial vanishes to order at least two."""
    a,b = weight(j,r),-weight(d,s)
    g = gcd(a,b)
    return [2,[[1,0,a//g],[0,1,b//g]]]


def expansion(j,d,r,s,L,terms,length):
    xs = row_powers(d,s,L,length)
    ys = row_powers(j,r,L,length)
    result = [0]*length
    for i,v,c in terms:
        product = multiply(xs[i],ys[v])
        result = [a+c*b for a,b in zip(result,product)]
    return result


def check_individual(j,d,r,s,L,h,H,terms):
    """Recover part of the denominator using additional local coefficients."""
    exponent = 15
    for p in (2,3,5,7,11,13):
        f, power = 0, 1
        while L%(p*power)==0:
            f, power = f+1, p*power
        if (H*power**h)**exponent < HEIGHT**h:
            continue
        e0 = 1
        while p**(e0*exponent)<HEIGHT:
            e0 += 1
        assert e0>f
        length = (h*e0 + e0-f-1)//(e0-f)
        coefficients = expansion(j,d,r,s,L,terms,length)
        assert not any(coefficients[:h])
        deficit = 0
        for t in range(h,length):
            z = coefficients[t]
            if z:
                v = 0
                while z%p==0:
                    z //= p
                    v += 1
                deficit = max(deficit, h*e0-t*(e0-f)-v)
        assert (H*p**deficit)**exponent < HEIGHT**h, (j,d,r,s,p,"individual bound")


def check(j,d,r,s,certificate):
    h,terms = certificate
    assert h>=2 and terms and all(c and 0<=i<d and 0<=v<j for i,v,c in terms)
    assert len({(i,v) for i,v,c in terms})==len(terms)
    highest = max(j*i+d*v for i,v,c in terms)
    assert highest*16 <= j*d*h
    L = lcm(denominator(d,s),denominator(j,r))
    assert expansion(j,d,r,s,L,terms,h)==[0]*h, (j,d,r,s,"local divisibility")

    lo = endpoint(d)-s,endpoint(j)-r
    hi = endpoint(d)+d-s,endpoint(j)+j-r
    def positive(sign):
        bound = []
        for i,v,c in terms:
            ends = lo if sign*c>0 else hi
            bound.append((j*i+d*v,sign*c*ends[0]**i*ends[1]**v))
        return all(sum(b*comb(w,t) for w,b in bound if w>=t)>=int(t==0)
                   for t in range(highest+1))

    assert positive(1) or positive(-1), (j,d,r,s,"nonvanishing")
    H = max(sum(abs(c)*hi[0]**i*hi[1]**v for i,v,c in terms if c*sign>0)
            for sign in (1,-1))
    D = lcm(*range(1,d))
    assert D%L==0
    assert H**16*D**h < HEIGHT**h, (j,d,r,s,"aggregate bound")
    check_individual(j,d,r,s,L,h,H,terms)
    return h,highest,H,D


@lru_cache(None)
def decade_endpoint(k, decade):
    return floor_root(factorial(k)*10**decade,k)


def aggregate17_decade(j,d,r,s,certificate):
    """First integer decade >=128 passing this certificate's size test."""
    h,terms = certificate
    D = lcm(*range(1,d))
    assert all(17*(j*i+d*v)<j*d*h for i,v,_ in terms)
    def test(decade):
        ends = decade_endpoint(d,decade)+d-s,decade_endpoint(j,decade)+j-r
        H = max(sum(abs(c)*ends[0]**i*ends[1]**v for i,v,c in terms if c*sign>0)
                for sign in (-1,1))
        return H**17 * D**h < 10**(decade*h)
    decade = 128
    while not test(decade):
        decade += 1
    return decade


def main(frontier=False):
    with gzip.open(DATA,"rt",encoding="ascii") as handle:
        data = json.load(handle)
    total = 0
    max_decade = 128
    for d in range(8,FIRST_DEEP_COLUMN):
        cutoffs = []
        for j in range(7,d):
            pair_decade = 128
            for r in range(j):
                for s in range(d):
                    key = f"{j},{d},{r},{s}"
                    certificate = data.pop(key,None) or tangent(j,d,r,s)
                    check(j,d,r,s,certificate)
                    if frontier:
                        pair_decade = max(pair_decade,aggregate17_decade(j,d,r,s,certificate))
                    total += 1
            cutoffs.append(pair_decade)
        if frontier:
            print(f"d={d}, j=7,...,{d-1}: {cutoffs}")
            max_decade = max(max_decade,max(cutoffs))
    assert not data
    k = FIRST_DEEP_COLUMN
    assert (endpoint(k)+k)**16 < HEIGHT and 16<=k
    print(f"Checked {total} branches and all largest columns from {k} upward.")
    print("Every five-row value above 10^128 has at least 17 distinct prime divisors.")
    print("Every full prime power in such a value satisfies P^15 < a.")
    if frontier:
        while (decade_endpoint(k,max_decade)+k)**17>=10**max_decade:
            max_decade += 1
        print(f"All pairs, including d>={k}, imply at least 18 primes at 10^{max_decade} and above.")


if __name__=="__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontier",action="store_true",help="test the 17-factor aggregate bound by decade")
    main(parser.parse_args().frontier)
