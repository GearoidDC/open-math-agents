"""Replay centered-row Chebyshev certificates using only Python's standard library."""
import gzip
import json
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, factorial, gcd, prod
from pathlib import Path

from Erdos849LocalInterpolation import floor_root


def ceil(x):
    return -((-x.numerator)//x.denominator)


@lru_cache(None)
def exponents(cols,n):
    """Reconstruct the stored coefficient order by weighted degree."""
    g = 1
    for k in cols:
        g = g*k//gcd(g, k)
    exps = sorted(
        product(*(range(k) for k in cols)),
        key=lambda es: sum(e*(g//k) for e,k in zip(es, cols)),
    )
    assert 0 < n <= len(exps)
    return g, exps[:n]


@lru_cache(None)
def chebyshev(lo,max_weight,degree):
    # With T_j((z+z^-1)/2)=(z^j+z^-j)/2, obtain nonnegative
    # Fourier coefficients by repeated multiplication of a Laurent polynomial.
    D=1000
    row=[1]
    denominator=1
    powers=[]
    for w in range(max_weight+1):
        powers.append(([v*(2 if i else 1) for i,v in enumerate(row[:degree+1])],denominator))
        old=row+[0,0]
        mid=2*(D+lo)
        side=D-lo
        row=[mid*old[0]+2*side*old[1]]
        row.extend(mid*old[j]+side*(old[j-1]+old[j+1]) for j in range(1,w+2))
        denominator*=4*D
    return powers


@lru_cache(None)
def projections(cols,n,degree,lower,upper):
    """Bound each centered monomial by a Chebyshev polynomial and an error."""
    g,exps=exponents(cols,n)
    weights=[sum(e*(g//k) for e,k in zip(es,cols)) for es in exps]
    D=1000
    lo=floor_root(D**g//10**(upper-lower),g)
    assert 0<lo<D
    powers=chebyshev(lo,max(weights),degree)
    K=1<<100
    scale=1<<128
    roots=[]
    growth=[]
    for k in cols:
        root=Fraction(2*floor_root(factorial(k)*10**upper*K**k,k),K)
        bottom=2*floor_root(factorial(k)*10**lower,k)
        loss=Fraction(sum(r*r for r in range(k-1,0,-2)),bottom*bottom)
        assert 0<=loss<1
        roots.append(root)
        growth.append((1+2/(K*root))/(1-loss))
    out=[]
    for w,es in zip(weights,exps):
        amp=scale*prod(a**e for a,e in zip(roots,es))
        row,den=powers[w]
        co=[v*amp.numerator//(den*amp.denominator) for v in row]
        # The sum of absolute omitted coefficients also bounds the omitted
        # function, since |T_j|<=1 and all coefficients are nonnegative.
        err=ceil(amp*prod(t**e for t,e in zip(growth,es))-sum(co))
        out.append((co+[0]*(degree+1-len(co)),max(1,err)))
    return out,scale


def local_check(cols,ofs,p,n,cs):
    """Check the N Newton interpolation samples on a smooth p-adic disk."""
    _,exps=exponents(cols,n)
    q=p**n
    a0=comb(ofs[0],cols[0])%p
    assert all(comb(r,k)%p==a0 for k,r in zip(cols,ofs))
    for t in range(n):
        a=a0+p*t
        table=[]
        for k,r in zip(cols,ofs):
            x=r
            digits=1
            while digits<n:
                digits=min(n,2*digits)
                mod=p**digits
                factors=[x-h for h in range(k)]
                der=sum(prod(factors[:h]+factors[h+1:]) for h in range(k))
                x=(x-(prod(factors)-factorial(k)*a)*pow(der,-1,mod))%mod
            assert (prod(x-h for h in range(k))-factorial(k)*a)%q==0
            table.append([pow(2*x-(k-1),e,q) for e in range(k)])
        v=[prod(tab[e] for tab,e in zip(table,es))%q for es in exps]
        assert all(sum(z*c for z,c in zip(v,row))%q==0 for row in cs)


def excluded(a,error,slope,q,u,b):
    # The interval is [(u-1)/b,(u+1)/b]. Evaluate T_j(u/b)
    # with the integers b^j T_j(u/b). The slope bound is Markov's
    # inequality |T'_j|<=j^2 on [-1,1].
    numer=0
    scale=1
    prev,term=0,1
    for j,c in enumerate(a):
        if j:
            scale*=b
            prev,term=term,(u if j==1 else 2*u*term-b*b*prev)
            numer*=b
        numer+=c*term
    radius=error*scale+(slope*scale+b-1)//b
    # Open intervals between consecutive multiples, with strict endpoints.
    return (numer-radius-1)//(q*scale)==(numer+radius)//(q*scale)


def real_check(cols,n,degree,lower,upper,flip,rows,p,depth_limit):
    _,exps=exponents(cols,n)
    sign=[(-1)**sum(e*f for e,f in zip(es,flip)) for es in exps]
    for low in range(lower,upper,3):
        tabs,scale=projections(cols,n,degree,low,min(upper,low+3))
        polys = []
        for row in rows:
            cs = [c*s for c,s in zip(row, sign)]
            coeff = [
                sum(c*values[j] for c,(values,_) in zip(cs, tabs))
                for j in range(degree+1)
            ]
            err = sum(abs(c)*e for c,(_,e) in zip(cs, tabs))
            while coeff and coeff[-1] == 0:
                coeff.pop()
            if coeff:
                slope = sum(i*i*abs(c) for i,c in enumerate(coeff))
                polys.append((coeff, err, slope))
        q = p**n*scale
        stack = [(0,1)]
        while stack:
            u,b = stack.pop()
            if any(excluded(a,r,m,q,u,b) for a,r,m in polys):
                continue
            assert b < 1 << depth_limit, (cols,flip,low,u,b)
            stack.extend(((2*u-1,2*b), (2*u+1,2*b)))


def verify(payload):
    if not __debug__:
        raise RuntimeError("Enable Python assertions to run the certificate checks.")
    col,ofs,p,lower,upper,n,degree,rows,covers=payload[:9]
    cols=tuple(col)
    assert (p,cols,lower,upper)==(107,(8,7,5,3),136,185)
    assert len(ofs)==4 and all(0<=r<p for r in ofs)
    assert type(n) is int and type(degree) is int and n>0 and degree>=0
    assert rows and all(len(row)==n and all(type(c) is int for c in row) for row in rows)
    assert len(payload)==9 or payload[9]=='real_data'
    local_check(cols,ofs,p,n,rows)
    flips=[tuple(f) for f,_,_,_ in covers]
    assert sorted(flips)==list(product(*[range(2) if k%2==0 else [0] for k in cols]))
    for f,ix,_,depth in covers:
        assert all(0<=i<len(rows) for i in ix) and 0<=depth<=17
        real_check(cols,n,degree,lower,upper,f,[rows[i] for i in ix],p,depth)
    return tuple(ofs)


if __name__=='__main__':
    cols=(8,7,5,3)
    p=107
    expected=set()
    for a in range(1,p):
        fibers = [
            [r for r in range(p) if comb(r,k)%p == a and (k%2 or r <= (k-1-r)%p)]
            for k in cols
        ]
        expected.update(product(*fibers))
    with gzip.open(Path(__file__).with_suffix('.json.gz'),'rt') as fh:
        records=json.load(fh)
    checked=set()
    for record in records:
        ofs=verify(record)
        assert ofs not in checked
        checked.add(ofs)
        print('Certified residue class',ofs,flush=True)
    assert checked==expected and len(expected)==20
    print('All 20 canonical classes with nonzero common value modulo 107 were excluded.')
