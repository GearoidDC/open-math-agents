"""Verify finite scalar sieves on smooth residue classes of the individual (5,8) curve."""

import json
import gzip
import sys
from fractions import Fraction
from functools import cache
from math import comb, factorial, lcm, prod
from pathlib import Path

from Erdos849CellSieve import primes,range_sieve
from Erdos849SaturatedCells import add,multiply,product_polynomial
from Erdos849RawCellTools import check_local,integer_valued,missing_denominator,normal_form,slope_bounds


@cache
def powers(i,j,depth):
    left=tuple(range(5));right=tuple(range(8))
    rel=product_polynomial(left,0,(1,0));del rel[5,0]
    rel={key:-c for key,c in rel.items()}
    add(rel,product_polynomial(right,j,(0,1)),Fraction(1,336))
    Z={}
    add(Z,product_polynomial([v for v in left if v!=i],0,(1,0)),
        Fraction(missing_denominator(5,8,i,j),120),offset_y=-1)
    out=[];power={(0,0):1}
    for d in range(1,depth+1):
        expanded=multiply(power,Z);add(expanded,power,1-d)
        for u in range(8,4,-1):
            for key in [key for key in expanded if key[0]==u]:
                add(expanded,rel,expanded.pop(key),u-5,key[1])
        power={key:Fraction(c,d) for key,c in expanded.items() if c}
        out.append(power)
    return out


@cache
def coefficient_matrix(i,j,depth):
    polys=powers(i,j,depth)
    rows=[]
    for key in set().union(*(p.keys() for p in polys)):
        terms=[(t,p[key]) for t,p in enumerate(polys) if key in p]
        den=lcm(*(c.denominator for _,c in terms))
        rows.append((key,den,[(t,int(c*den)) for t,c in terms]))
    return rows


def reconstruct(i,j,cs):
    poly={}
    for key,den,row in coefficient_matrix(i,j,len(cs)):
        s=sum(cs[t]*v for t,v in row)
        if s:poly[key]=Fraction(s,den)
    return poly


@cache
def points(i,j,p,extras):
    images={k:[comb(x,k)%p for x in range(p)] for k in (5,8,*extras)}
    allowed=set(range(p))
    for k in extras:allowed.intersection_update(images[k])
    left={}
    for x,v in enumerate(images[5]):
        if v in allowed:left.setdefault(v,[]).append(x)
    return [(x,m) for m,v in enumerate(images[8]) for x in left.get(v,[]) if (x,m)!=(i,j)]


@cache
def packed(i,j,depth,p,extras):
    pts=points(i,j,p,extras)
    width=(depth*(p-1)**2).bit_length()
    mask=(1<<width)-1
    polynomials=powers(i,j,depth)
    terms={key for P in polynomials for key in P if key[1]<=0}
    inner=(len(terms)*(p-1)**2).bit_length()
    inner_mask=(1<<inner)-1
    monomials={}
    for u,v in terms:
        acc=0
        for x,m in reversed(pts):
            y=m-j
            # On y=0 use minus the y-constant polynomial part, then add binom(Z,t).
            val=(pow(x,u,p)*pow(y,v,p)%p if y and v<0 else
                 (-pow(x,u,p))%p if not y and v==0 else 0)
            acc=(acc<<inner)+val
        monomials[u,v]=acc
    den=missing_denominator(5,8,i,j)
    Z={k:den*factorial(j)*factorial(7-j)*(-1)**(7-j)*pow(40320*(x-i),-1,p)%p
       for k,(x,m) in enumerate(pts) if m==j}
    packed_rows=[]
    for t,P in enumerate(polynomials,1):
        s=sum(monomials[key]*(c.numerator*pow(c.denominator,-1,p)%p)
              for key,c in P.items() if key in monomials)
        chunks=[]
        for k in range(len(pts)):
            chunks.append(((s&inner_mask)+(comb(Z[k],t) if k in Z else 0))%p);s>>=inner
        assert s==0
        packed_rows.append(sum(v<<(width*k) for k,v in enumerate(chunks)))
    return packed_rows,width,mask,len(pts)


def scalar_image(i,j,cs,p,extras,Q):
    rows,width,mask,n=packed(i,j,len(cs),p,tuple(extras))
    inv=pow(Q,-1,p)
    value=sum((c*inv%p)*r for c,r in zip(cs,rows))
    values=set()
    for _ in range(n):
        values.add((value&mask)%p);value>>=width
    assert value==0
    return values


def direct_scalar(i,j,cs,p,Q):
    """Cross-check the packed arithmetic by evaluating the defining integral expression."""
    regular=[(u,v,c.numerator*pow(c.denominator,-1,p)%p)
             for (u,v),c in reconstruct(i,j,cs).items() if v>=0]
    D=missing_denominator(5,8,i,j);values=set()
    for x in range(p):
        for m in range(p):
            if comb(x,5)%p!=comb(m,8)%p:continue
            lhs=D*prod(x-t for t in range(5) if t!=i)
            rhs=D*prod(m-t for t in range(8) if t!=j)
            for z in range(p):
                if (120*(m-j)*z-lhs)%p or (40320*(x-i)*z-rhs)%p:continue
                val=sum(c*comb(z,t) for t,c in enumerate(cs,1))
                val-=sum(c*pow(x,u,p)*pow(m-j,v,p) for u,v,c in regular)
                values.add(val*pow(Q,-1,p)%p)
    return values


def analyze(i,j,p,x,m,height,E,cs,extras=(),limit=383,max_cap=None):
    poly=reconstruct(i,j,cs)
    integer_valued({key:c for key,c in poly.items() if key[1]>=0})
    assert check_local(5,8,i,j,cs,p,E,x,m,poly)
    base,lo,hi=slope_bounds(5,8,height);Q=p**E
    rem={key:c for key,c in poly.items() if key[1]<0}
    weight=lambda key:8*key[0]+5*key[1]
    lead=max(rem,key=weight);assert weight(lead)<0
    sizes={key:abs(c)*hi**key[0]*Fraction(base)**weight(key) for key,c in rem.items()}
    size=sum(sizes.values());cap=int(size//Q)
    lower=abs(rem[lead])*lo**lead[0]*Fraction(base)**weight(lead)
    sign=(1 if rem[lead]>0 else -1) if lower>size-sizes[lead] else 0
    if sign and cap==0:return 0,[]
    if max_cap is not None and cap>max_cap:return cap,None
    good=[s for s in primes(limit) if s>max(8,len(cs)) and s!=p]
    if cap<=4096:
        candidates=list(range(1 if sign>0 else -cap,0 if sign<0 else cap+1))
        for s in good:
            ids=scalar_image(i,j,cs,s,extras,Q)
            candidates=[v for v in candidates if v%s in ids]
            if not candidates:break
        survivors=candidates
    else:
        rules=[(s,scalar_image(i,j,cs,s,extras,Q)) for s in good]
        survivors=range_sieve(cap,rules)
        survivors=[v for v in survivors if not sign or sign*v>0]
    if survivors:
        for s in primes(997):
            if s<=limit or s==p:continue
            ids=scalar_image(i,j,cs,s,extras,Q)
            survivors=[v for v in survivors if v%s in ids]
            if not survivors:break
    return cap,survivors


def reflect(cs):
    return [sum((-1)**t*comb(t-1,r-1)*cs[t-1] for t in range(r,len(cs)+1))
            for r in range(1,len(cs)+1)]


def verify_record(i,j,record,include_reflected=True,limit=383):
    p=record['p'];height=record['height'];raw=record['branches']
    targets=[(i,j,False)]
    if include_reflected and (i,j)!=(i,7-j):targets.append((i,7-j,True))
    stats=[]
    for a,b,flip in targets:
        expected=set(points(a,b,p,()));seen=set();maxcap=0
        for xx,mm,E,coefficients in raw:
            x=xx;m=(7-mm)%p if flip else mm
            assert (x,m) in expected and (x,m) not in seen
            cs=reflect(coefficients) if flip else coefficients
            if not seen:
                assert reconstruct(a,b,cs)==normal_form(5,8,a,b,cs)
                controls=[s for s in primes(97) if s>max(len(cs),8) and s!=p][:2]
                assert len(controls)==2
                for s in controls:
                    assert scalar_image(a,b,cs,s,(),p**E)==direct_scalar(a,b,cs,s,p**E)
            cap,survivors=analyze(a,b,p,x,m,height,E,cs,limit=limit)
            assert not survivors,(a,b,x,m,cap,survivors)
            maxcap=max(maxcap,cap);seen.add((x,m))
        assert seen==expected
        stats.append((a,b,height,p,len(seen),maxcap))
        packed.cache_clear()
        coefficient_matrix.cache_clear()
        powers.cache_clear()
        points.cache_clear()
    return stats


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Enable assertions.')
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files',nargs='*',type=Path)
    parser.add_argument('--all-cells',action='store_true')
    parser.add_argument('--require-offsets',type=lambda s:tuple(map(int,s.split(','))),default=())
    options=parser.parse_args()
    files=options.files or [Path(__file__).with_suffix('.json.gz')]
    seen=set()
    for name in files:
        data=json.loads(gzip.decompress(name.read_bytes()))
        for key,record in data.items():
            i,j=map(int,key.split(','));stats=verify_record(i,j,record)
            print(stats,flush=True)
            for a,b,height,_,_,_ in stats:
                assert height<=136 and (a,b) not in seen
                seen.add((a,b))
    offsets=range(8) if options.all_cells else options.require_offsets
    assert all(0<=j<8 and all((i,j) in seen for i in range(5)) for j in offsets)
    print('Occupied cells at height 136:',len(seen),flush=True)
