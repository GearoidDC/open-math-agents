"""Exact local polynomial and finite prime-power checks in four binomial columns."""

from functools import lru_cache, reduce
from itertools import combinations, product
from math import factorial, gcd, lcm, prod
from pathlib import Path
import gzip
import json

from Erdos849EightSmoothTail import expansion
from Erdos849InterpolatedPowers import denominator, floor_root, row_powers
from Erdos849SmoothNeighbors import PRIMES


@lru_cache(None)
def monomials(columns, count):
    common = lcm(*columns)
    by_weight = {}
    for es in product(*(range(k) for k in columns)):
        w = sum(e*(common//k) for e,k in zip(es,columns))
        if w:
            by_weight.setdefault(w,es)
    return sorted(by_weight.items())[:count]


def candidates(columns, offsets, count):
    mons = monomials(columns,count)
    length = count+2
    divisor = lcm(*(denominator(k,s) for k,s in zip(columns,offsets)))
    rows = [row_powers(k,s,divisor,length) for k,s in zip(columns,offsets)]
    pivots = {}
    for index, (_, es) in enumerate(mons):
        values = expansion(rows,es,length)
        coeff = [0]*index+[1]
        assert values[0] == 0
        for h in range(1,length):
            if values[h] == 0:
                continue
            if h not in pivots:
                pivots[h] = values,coeff
                yield h, [(c,w,es) for c,(w,es) in zip(coeff,mons) if c]
                break
            old, vector = pivots[h]
            g = gcd(old[h],values[h])
            a,b = old[h]//g,values[h]//g
            coeff = [a*c-(b*vector[j] if j<len(vector) else 0)
                     for j,c in enumerate(coeff)]
            values = [a*x-b*y for x,y in zip(values,old)]
            content = reduce(gcd,coeff)
            assert all(x%content == 0 for x in values)
            coeff = [x//content for x in coeff]
            values = [x//content for x in values]


@lru_cache(None)
def root(column,decade):
    return floor_root(factorial(column)*10**decade,column)


def extra_bounds(columns,offsets,terms,decade):
    lo = [root(k,decade)-s for k,s in zip(columns,offsets)]
    hi = [v+k for k,v in zip(columns,lo)]
    sign = 1 if terms[-1][0] > 0 else -1
    total = plus = minus = 0
    positive = True
    for c,w,es in reversed(terms):
        c *= sign
        upper = prod(x**e for x,e in zip(hi,es))
        if c>0:
            plus += c*upper
            total += c*prod(x**e for x,e in zip(lo,es))
        else:
            minus -= c*upper
            total += c*upper
        if total <= 0:
            positive = False
    return positive, max(plus,minus)


def certificate_bounds(columns,offsets,h,terms,decade):
    positive,height = extra_bounds(columns,offsets,terms,decade)
    return positive, height, terms[-1][1]


@lru_cache(None)
def lagrange_powers(k,s,divisor,h):
    """Reconstruct branch powers by Lagrange inversion, independently of discovery."""
    a = divisor*factorial(k)//prod(s-v for v in range(k) if s!=v)
    phi = [1]
    for v in range(k):
        if v==s:
            continue
        assert a%(s-v)==0
        factor = a//(s-v)
        phi = [x+factor*y for x,y in zip(phi+[0],[0]+phi)]
    powers = [[0]*h for _ in range(k)]
    powers[0][0] = 1
    for m in range(1,h):
        # inv = phi(u)^(-m), using phi*inv' = -m*phi'*inv.
        inv = [1]
        for j in range(1,m):
            numerator = -sum(((m-1)*i+j)*phi[i]*inv[j-i]
                             for i in range(1,min(j,k-1)+1))
            assert numerator%j==0
            inv.append(numerator//j)
        for e in range(1,min(k,m+1)):
            numerator = a**e*e*inv[m-e]
            assert numerator%m==0
            powers[e][m] = numerator//m
    return powers


def check_piece(columns,offsets,h,terms,decade,budget,rate):
    assert len(columns)==len(offsets)
    common = lcm(*columns)
    previous = 0
    for c,w,es in terms:
        assert len(es)==len(columns) and c and all(0<=e<k for e,k in zip(es,columns))
        assert w==sum(e*(common//k) for e,k in zip(es,columns)) and w>previous
        previous = w
    good,height,weight = certificate_bounds(columns,offsets,h,terms,decade)
    assert good and height < budget**h and weight*rate <= common*h
    divisor = lcm(*(denominator(k,s) for k,s in zip(columns,offsets)))
    assert 420%divisor==0
    rows = [lagrange_powers(k,s,divisor,h) for k,s in zip(columns,offsets)]
    total = [0]*h
    for c,w,es in terms:
        vals = expansion(rows,es,h)
        total = [u+c*v for u,v in zip(total,vals)]
    assert not any(total)


def discrete_tail(decade,budget,rate,large=5,minimum=None):
    """Bound a product of up to large unknown and 25 prescribed prime powers."""
    cap = 25+large
    assert rate>cap and len(PRIMES)==25
    D = 420
    start = 10**decade
    end = decade
    # For a >= 10^end we use D*budget^30*(a/start)^(30/rate) < a.
    while (D*budget**cap)**rate >= start**cap*10**(end*(rate-cap)):
        end += 1
    if minimum is None:
        minimum = decade
    assert minimum>=decade
    for step in range(10*minimum,10*end):
        # Upper bound for budget*(a/start)^(1/rate) on this tenth-decade.
        q = 1+floor_root(budget**(10*rate)*10**(step+1-10*decade),10*rate)
        maximum = D*q**large
        for p in PRIMES:
            power = 1
            while power*p<=q:
                power *= p
            maximum *= power
        assert maximum**10 < 10**step, (step,q)
    return end


def valuation(n,p):
    assert n
    v = 0
    while n%p==0:
        n //= p
        v += 1
    return v


def host_loss(offsets,p):
    """Maximum cofactor and denominator loss at these column-eight positions."""
    modulus = p
    while modulus<=8:
        modulus *= p
    maximum = 0
    for n in range(modulus):
        vals = [valuation((n-i)%modulus or modulus,p) for i in range(8)]
        host = vals.index(max(vals))
        e = sum(vals)-valuation(factorial(8),p)
        assert 0<=e<=vals[host]
        loss = sum(vals[i] for i in offsets)
        if host in offsets:
            loss -= e
            # A zero residue may hide additional powers of p; those
            # raise the numerator valuation and the hosted e equally.
            if e or (n-host)%modulus==0:
                loss += valuation(420,p)
        maximum = max(maximum,loss)
    return p**maximum


def check_hosts(decade,budget,rate):
    constants = [max(prod(host_loss(offsets,p) for p in (2,3,5,7))
                     for offsets in combinations(range(8),size)) for size in (1,2)]
    assert constants == [117600,705600]
    L = root(8,decade)-7
    assert rate>=24 and L>constants[0]*budget**2 and L**2>constants[1]*budget**6


def main():
    columns = (8,7,5,3)
    decade,budget,rate = 128,34800,36
    with gzip.open(Path(__file__).with_suffix(".json.gz"),"rt",encoding="ascii") as handle:
        pieces = json.load(handle)
    assert sorted(tuple(p[0]) for p in pieces)==list(product(*(range(k) for k in columns)))
    for offsets,h,terms in pieces:
        check_piece(columns,tuple(offsets),h,terms,decade,budget,rate)
    check_hosts(decade,budget,rate)
    end = discrete_tail(decade,budget,rate,6)
    print(f"Verified {len(pieces)} four-column branches, discrete products from "
          f"10^{decade} through 10^{end}, and the continuous tail.")
    print("These columns force at least 31 distinct prime divisors, including "
          "at least seven above 100 before the separate congruence check.")


if __name__=="__main__":
    main()
