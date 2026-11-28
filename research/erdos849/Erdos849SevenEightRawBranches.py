"""Check individual prime assignments on each smooth residue branch of columns 7 and 8."""

import gzip
import json
from collections import defaultdict
from fractions import Fraction
from functools import cache
from math import comb, factorial, lcm, prod
from pathlib import Path

from Erdos849CellSieve import primes, range_sieve
from Erdos849RawCellTools import (binomial_forms, check_local, falling, integer_valued, missing_denominator,
                                  normal_form, slope_bounds)
from Erdos849SevenEightRawEdges import reflected


@cache
def points(i,j,p):
    left=defaultdict(list)
    for x in range(p):
        left[comb(x,7)%p].append(x)
    return [(x,m) for m in range(p) for x in left[comb(m,8)%p] if (x,m)!=(i,j)]


def modulo(value,p):
    return value.numerator*pow(value.denominator,-1,p)%p


class Family:
    def __init__(self,i,j,depth,height):
        self.i,self.j,self.depth=i,j,depth
        self.forms=list(binomial_forms(7,8,i,j,depth))
        self.rows=[]
        for key in set().union(*(f.keys() for f in self.forms)):
            col=[(t,f[key]) for t,f in enumerate(self.forms) if key in f]
            den=lcm(*(c.denominator for _,c in col))
            self.rows.append((key,den,[(t,int(c*den)) for t,c in col]))
        base,self.lo,self.hi=slope_bounds(7,8,height)
        self.factors={key:Fraction(base)**(8*key[0]+7*key[1]) for key,_,_ in self.rows if key[1]<0}
        self.packed={}

    def polynomial(self,cs):
        poly={}
        for key,den,column in self.rows:
            s=sum(cs[t]*v for t,v in column)
            if s:poly[key]=Fraction(s,den)
        return poly

    def bound(self,poly,Q):
        rem={key:v for key,v in poly.items() if key[1]<0}
        weight=lambda key:8*key[0]+7*key[1]
        lead=max(rem,key=weight)
        assert weight(lead)<0
        sizes={key:abs(c)*self.hi**key[0]*self.factors[key] for key,c in rem.items()}
        upper=sum(sizes.values())
        lower=abs(rem[lead])*self.lo**lead[0]*self.factors[lead]
        sign=(1 if rem[lead]>0 else -1) if lower>upper-sizes[lead] else 0
        return int(upper//Q),sign

    def modular_rows(self,p):
        i,j=self.i,self.j
        pts=points(i,j,p)
        keys=[key for key,_,_ in self.rows if key[1]<=0]
        width=(len(keys)*(p-1)**2).bit_length()
        mask=(1<<width)-1
        terms={}
        for u,v in keys:
            encoded=0
            for x,m in reversed(pts):
                # At y=0, evaluate binom(Z,t) minus the regular constant term.
                a=(pow(x,u,p)*pow(m-j,v,p)%p if m!=j and v<0 else
                   (-pow(x,u,p))%p if m==j and v==0 else 0)
                encoded=(encoded<<width)+a
            terms[u,v]=encoded
        D=missing_denominator(7,8,i,j)
        zero={n:D*prod(j-r for r in range(8) if r!=j)*pow(factorial(8)*(x-i),-1,p)%p
              for n,(x,m) in enumerate(pts) if m==j}
        stride=(self.depth*(p-1)**2).bit_length()
        rows=[]
        for t,F in enumerate(self.forms,1):
            encoded=sum(modulo(c,p)*terms[key] for key,c in F.items() if key in terms)
            row=0
            for n in range(len(pts)):
                v=((encoded&mask)+(comb(zero[n],t) if n in zero else 0))%p
                row|=v<<(stride*n)
                encoded>>=width
            assert encoded==0
            rows.append(row)
        return rows,stride,len(pts)

    def image(self,cs,p,Q):
        if p not in self.packed:self.packed[p]=self.modular_rows(p)
        rows,stride,n=self.packed[p]
        inv=pow(Q,-1,p);mask=(1<<stride)-1
        encoded=sum((c*inv%p)*row for c,row in zip(cs,rows))
        values=set()
        for _ in range(n):
            values.add((encoded&mask)%p);encoded>>=stride
        assert encoded==0
        return values

    def direct_image(self,poly,cs,p,Q):
        i,j=self.i,self.j;D=missing_denominator(7,8,i,j)
        reg=[(u,v,modulo(c,p)) for (u,v),c in poly.items() if v>=0]
        values=set()
        residues=[(x,m) for x in range(p) for m in range(p) if (x,m)!=(i,j)
                  and (8*falling(x,7)-falling(m,8))%p==0]
        assert set(residues)==set(points(i,j,p))
        for x,m in residues:
            if x!=i:
                z=D*prod(m-r for r in range(8) if r!=j)*pow(factorial(8)*(x-i),-1,p)%p
            else:
                z=D*prod(x-r for r in range(7) if r!=i)*pow(factorial(7)*(m-j),-1,p)%p
            scalar=sum(c*comb(z,t) for t,c in enumerate(cs,1))
            scalar-=sum(c*pow(x,u,p)*pow(m-j,v,p) for u,v,c in reg)
            values.add(scalar*pow(Q,-1,p)%p)
        return values

    def check(self,cs,p,E,x,m,control):
        assert len(cs)==self.depth
        poly=self.polynomial(cs)
        if control:assert poly==normal_form(7,8,self.i,self.j,cs)
        integer_valued({key:c for key,c in poly.items() if key[1]>=0})
        check_local(7,8,self.i,self.j,cs,p,E,x,m,poly)
        Q=p**E;cap,sign=self.bound(poly,Q)
        good=[s for s in primes(997) if s>max(8,len(cs)) and s!=p]
        if control:
            for s in good[:2]:assert self.image(cs,s,Q)==self.direct_image(poly,cs,s,Q)
        if sign and cap==0:return cap
        first=[s for s in good if s<=383]
        candidates=range_sieve(cap,[(s,self.image(cs,s,Q)) for s in first])
        candidates=[v for v in candidates if not sign or sign*v>0]
        for s in good[len(first):]:
            if not candidates:break
            ids=self.image(cs,s,Q)
            candidates=[v for v in candidates if v%s in ids]
        assert not candidates,(self.i,self.j,x,m,cap,candidates)
        return cap


def verify(record,flip=False):
    i,j=record["cell"];p=record["prime"];height=record["height"]
    if flip:j=7-j
    branches=record["branches"]
    family=Family(i,j,len(branches[0][3]),height)
    remaining=set(points(i,j,p));maxcap=0
    for t,(x,m,E,cs) in enumerate(branches):
        if flip:m=(7-m)%p;cs=reflected(cs)
        remaining.remove((x,m))
        cap=family.check(cs,p,E,x,m,t==0)
        maxcap=max(maxcap,cap)
    assert not remaining
    return i,j,height,p,len(branches),maxcap


if __name__=="__main__":
    if not __debug__:raise RuntimeError("Enable assertions to verify the certificates")
    record=json.loads(gzip.decompress(Path(__file__).with_suffix(".json.gz").read_bytes()))
    assert record["cell"]==[3,3] and record["height"]<=136 and record["prime"]==761
    assert len(record["branches"])==866
    assert all(missing_denominator(7,8,3,j)==117600 for j in (3,4))
    for flip in (False,True):print(verify(record,flip),flush=True)
