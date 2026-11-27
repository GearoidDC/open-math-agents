"""Verify the large-height interpolation bound in the remaining nine- and ten-column cases."""

from functools import cache,reduce
from itertools import combinations, product
from math import gcd, lcm, prod

from Erdos849EightSmoothTail import expansion
from Erdos849InterpolatedPowers import denominator, floor_root, row_powers
from Erdos849PatternThree import root


DECADE=5000
CAP=31


@cache
def monomials(cols,count):
    W=lcm(*cols)
    return sorted((sum(e*(W//k) for k,e in zip(cols,es)),es)
                  for es in product(*(range(k) for k in cols)) if any(es))[:count]


def local_candidates(cols,offsets,count):
    L=lcm(*(denominator(k,s) for k,s in zip(cols,offsets)))
    mons=monomials(cols,count)
    hmax=count+2
    rows=[row_powers(k,s,L,hmax) for k,s in zip(cols,offsets)]
    pivots={}
    for index,(_,es) in enumerate(mons):
        series=expansion(rows,es,hmax)
        vector=[0]*index+[1]
        for h in range(1,hmax):
            if not series[h]:
                continue
            if h not in pivots:
                pivots[h]=(series,vector)
                yield h,[(c,w,v) for c,(w,v) in zip(vector,mons) if c]
                break
            old,other=pivots[h]
            g=gcd(old[h],series[h])
            a,b=old[h]//g,series[h]//g
            vector=[a*c-(b*other[j] if j<len(other) else 0) for j,c in enumerate(vector)]
            g=reduce(gcd,vector)
            combined=[a*x-b*y for x,y in zip(series,old)]
            assert all(v%g==0 for v in combined)
            series=[v//g for v in combined]
            vector=[x//g for x in vector]


def sized(cols,offsets,terms,h,Q):
    W=lcm(*cols)
    if CAP*terms[-1][1]>W*h:
        return False
    lower=[root(k,DECADE)-s for k,s in zip(cols,offsets)]
    upper=[v+k for k,v in zip(cols,lower)]
    signed=[[],[]]
    heights=[0,0]
    for c,w,es in terms:
        lo=abs(c)*prod(n**e for n,e in zip(lower,es))
        hi=abs(c)*prod(n**e for n,e in zip(upper,es))
        s=int(c<0)
        heights[s]+=hi
        signed[s].append((w,lo))
        signed[1-s].append((w,-hi))
    if max(heights)>=Q**h:
        return False
    for summands in signed:
        groups={}
        for w,c in summands:
            groups[w]=groups.get(w,0)+c
        total=0
        for w in sorted(groups,reverse=True):
            total+=groups[w]
            if total<=0:
                break
        else:
            return True
    return False


def check(cols,count=26):
    D=lcm(*range(1,max(cols)))
    Q=floor_root((10**DECADE-1)//D,CAP)
    order=0
    for offsets in product(*(range(k) for k in cols)):
        for h,terms in local_candidates(cols,offsets,count):
            if not sized(cols,offsets,terms,h,Q):
                continue
            L=lcm(*(denominator(k,s) for k,s in zip(cols,offsets)))
            assert D%L==0
            rows=[row_powers(k,s,L,h) for k,s in zip(cols,offsets)]
            full=[0]*h
            for c,_,es in terms:
                full=[a+c*b for a,b in zip(full,expansion(rows,es,h))]
            assert not any(full)
            order=max(order,h)
            break
        else:
            raise AssertionError((cols,offsets))
    print(f"{cols}: all {prod(cols)} offset tuples verified, highest order {order}.",flush=True)


if __name__=="__main__":
    for d in (9,10):
        for j,k in combinations((5,*range(7,d)),2):
            check((d,k,j))
