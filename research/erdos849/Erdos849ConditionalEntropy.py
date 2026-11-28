"""Verify the exclusion of exactly forty occupied tuples using Gaussian observations."""

import json
from fractions import Fraction
from functools import cache
from itertools import product
from math import comb,factorial,prod
from pathlib import Path

from Erdos849PositionEntropy import POLYS,intervals


def inverse_and_determinant(matrix):
    n=len(matrix)
    rows=[[Fraction(v) for v in row]+[Fraction(i==j) for j in range(n)]
          for i,row in enumerate(matrix)]
    det=Fraction(1)
    for i in range(n):
        pivot=rows[i][i]
        assert pivot>0
        det*=pivot
        rows[i]=[v/pivot for v in rows[i]]
        for j in range(n):
            if i!=j:
                multiplier=rows[j][i]
                rows[j]=[v-multiplier*w for v,w in zip(rows[j],rows[i])]
    assert det.denominator==1 and det>0
    adj=[]
    for row in rows:
        values=[v*det for v in row[n:]]
        assert all(v.denominator==1 for v in values)
        adj.append([int(v) for v in values])
    det=int(det)
    for i in range(n):
        for j in range(n):
            assert sum(matrix[i][q]*adj[q][j] for q in range(n))==det*int(i==j)
    return det,adj


@cache
def evaluation(k,e,s):
    return sum(c*comb(s,t) for t,c in enumerate(POLYS[k][e]))


def forty_upper(cols,scores):
    # Eight eighth-column offsets for each i must cover every seventh-column offset.
    caps={}
    fourth=3 if 3 in cols else 6
    for s,v in scores.items():
        t=s[cols.index(fourth)]
        shallow=t if fourth==3 else min(t,5-t)
        key=tuple(s[cols.index(k)] for k in (5,8,7))+(shallow,)
        caps[key]=max(caps.get(key,0),v)
    # Upward rounding of eight times each base-two logarithm, by an exact bit length.
    logs={v:(v**8).bit_length() for v in set(caps.values())}
    total=0
    for i in range(5):
        states={(0,0):0}
        for j in range(8):
            after={}
            for (mask,short),v in states.items():
                for k in range(7):
                    seen=mask|1<<k
                    if seen.bit_count()+7-j<7:continue
                    for t in range(3):
                        dest=seen,short|1<<t
                        after[dest]=max(after.get(dest,0),v+logs[caps[i,j,k,t]])
            states=after
        total+=states[127,7]
    return total


def verify(cols,height,data):
    digits,L,noise=data
    scale=prod(factorial(k-1) for k in cols)
    total=0;previous=Fraction(-1)
    for degrees,c in digits:
        assert len(degrees)==len(cols) and all(type(e)==int and 0<=e<k for e,k in zip(degrees,cols))
        assert type(c)==int and c>0
        weight=sum(Fraction(e,k) for e,k in zip(degrees,cols))
        bounds=[intervals(k,height)[e] for k,e in zip(cols,degrees)]
        lower,upper=map(prod,zip(*bounds))
        assert previous<weight<1 and total<lower
        total+=c*upper;previous=weight
    assert 420*total<10**height*scale
    rank=len(L)
    assert rank==len(noise)>0 and all(type(d)==int and d>0 for d in noise)
    assert all(len(row)==len(digits) and all(type(v)==int for v in row) for row in L)
    caps=[c for _,c in digits];variances=[c*(c+2) for c in caps]
    LH=[[a*v for a,v in zip(row,variances)] for row in L]
    covariance=[[sum(x*y for x,y in zip(r,t))+(noise[i] if i==j else 0)
                 for j,t in enumerate(L)] for i,r in enumerate(LH)]
    det,adj=inverse_and_determinant(covariance)
    grid=tuple(product(*(range(k) for k in cols)))
    scores={}
    for s in grid:
        vals=[prod(evaluation(k,e,t) for k,e,t in zip(cols,degrees,s)) for degrees,_ in digits]
        width=1+sum(c*abs(x) for c,x in zip(caps,vals))
        variance=1+sum(v*x*x for v,x in zip(variances,vals))
        cov=[sum(a*x for a,x in zip(row,vals)) for row in LH]
        conditional=variance*det-sum(x*sum(v*y for v,y in zip(row,cov)) for x,row in zip(cov,adj))
        assert conditional>=det
        scores[s]=min(40*det*width*width,57*conditional)
    flips=tuple(product((True,False),repeat=len(cols)))
    combined={s:prod(scores[tuple(t if b else k-1-t for k,t,b in zip(cols,s,f))] for f in flips)
              for s in grid}
    count=prod(c+1 for c in caps)
    upper=forty_upper(cols,combined)
    lower=(prod(noise)*count**2*(40*det)**40)**len(flips)
    assert lower**8>det**(8*len(flips))*(1<<upper)
    print(cols,height,len(digits),rank,'excludes forty distinct prime divisors',flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Enable assertions.')
    records=json.loads(Path(__file__).with_suffix('.json').read_text())
    assert len(records)==2 and {(tuple(cols),height) for cols,height,_ in records}=={
        ((8,7,5,3),185),((8,7,6,5),170)}
    for cols,height,data in records:
        verify(tuple(cols),height,data)
