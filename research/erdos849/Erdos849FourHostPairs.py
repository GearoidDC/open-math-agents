"""Count heavy numerator terms forced by individual and reflected prime assignments."""

import gzip
import json
from itertools import product
from math import factorial,lcm,prod
from pathlib import Path

from Erdos849ExactlyThirtyFive import small_prime_options
from Erdos849PatternThree import certificate_bounds,floor_root,root,valuation


def cell_caps(columns,archive,height):
    blocks=[[[0]*7 for _ in range(5)] for _ in range(8)]
    data=json.loads(gzip.decompress(Path(__file__).with_name(archive).read_bytes()))
    expected=set(product(*(range(k) for k in columns)))
    assert {tuple(offsets) for offsets,_,_ in data}==expected
    for offsets,order,terms in data:
        positive,bound,weight=certificate_bounds(columns,offsets,order,terms,height)
        assert positive and 0<36*weight<=lcm(*columns)*order
        s,i,j=offsets[0],offsets[columns.index(5)],offsets[1]
        q=1+floor_root(bound,order)
        blocks[s][i][j]=max(blocks[s][i][j],q)
    return blocks


def pair_products(left,right):
    """Largest product for each count of unknown primes on the two sides."""
    states={(0,0,0,0):1}
    for j in range(7):
        choices=[(0,0,0,1)]
        for i in range(5):
            bit=1<<i
            choices.extend([(1,0,bit,left[i][j]),(0,1,bit,right[i][j])])
            for k in range(i):
                both=bit|(1<<k)
                choices.extend([(2,0,both,left[i][j]*left[k][j]),
                                (0,2,both,right[i][j]*right[k][j]),
                                (1,1,both,max(left[i][j]*right[k][j],left[k][j]*right[i][j]))])
        next_states={}
        for (nl,nr,twice,mask),value in states.items():
            for l,r,seen,factor in choices:
                key=(nl+l,nr+r,twice+int(l+r==2),mask|seen)
                if key[0]<=4 and key[1]<=4 and key[2]<=1:
                    next_states[key]=max(value*factor,next_states.get(key,0))
        states=next_states
    result={}
    for (l,r,_,mask),upper in states.items():
        # The known factors can furnish at most 8-l-r further 5-offsets.
        if 5-mask.bit_count()<=8-l-r:
            result[l,r]=max(upper,result.get((l,r),0))
    assert set(result)==set(product(range(5),repeat=2))
    return result


def verify(columns,archive,height):
    blocks=cell_caps(columns,archive,height)
    lower=root(8,height)-7
    thresholds=[]
    for block in blocks:
        caps=sorted((v for row in block for v in row),reverse=True)
        thresholds.append([(lower+t-1)//t for c in range(5) for t in [prod(caps[:4-c])]])
    pair_threshold=[]
    for s in range(4):
        maxima=pair_products(blocks[s],blocks[7-s])
        pair_threshold.append({key:(lower**2+v-1)//v for key,v in maxima.items()})
    tested=0
    least=8
    for rows in product(*(small_prime_options(p) for p in (2,3,5,7))):
        known=[prod(row[s][0] for row in rows) for s in range(8)]
        count=[sum(row[s][1] for row in rows) for s in range(8)]
        heavy=[int(known[s]<thresholds[s][count[s]]) for s in range(8)]
        required=0
        for s in range(4):
            t=7-s
            cannot_both_be_light=known[s]*known[t]<pair_threshold[s][4-count[s],4-count[t]]
            required+=max(heavy[s]+heavy[t],int(cannot_both_be_light))
        least=min(least,required)
        tested+=1
    assert tested==11200 and least>=4
    print(columns,height,tested,least,'terms require at least five primes',flush=True)


def seven_options(p):
    modulus=p
    while modulus<=7:
        modulus*=p
    options=set()
    for r in range(modulus):
        vals=[valuation((r-j)%modulus or modulus,p) for j in range(7)]
        s=vals.index(max(vals))
        e=sum(vals)-valuation(factorial(7),p)
        assert 0<=e<=vals[s]
        known=[0]*7
        if r==s:
            vals[s]+=valuation(420,p)-e
        elif e:
            known[s]=1
        options.add(tuple((p**v,n) for v,n in zip(vals,known)))
    return options


def seven_thresholds(blocks,j,lower):
    # A five-prime term covers all five offsets and four reflected eighth blocks.
    states={(0,0):1}
    for i in range(5):
        following=states.copy()
        for (n,mask),v in states.items():
            for s in range(8):
                key=n+1,mask|1<<min(s,7-s)
                following[key]=max(following.get(key,0),v*blocks[s][i][j])
        states=following
    thresholds=[]
    for known in range(6):
        best=max(v for (n,mask),v in states.items() if n==5-known and 4-mask.bit_count()<=known)
        thresholds.append((lower+best-1)//best)
    return thresholds


def verify_seven(columns,archive,height,required):
    blocks=cell_caps(columns,archive,height)
    lower=root(7,height)-6
    thresholds=[seven_thresholds(blocks,j,lower) for j in range(7)]
    least=7
    for rows in product(*(seven_options(p) for p in (2,3,5,7))):
        heavy=0
        for j in range(7):
            bound=prod(row[j][0] for row in rows)
            known=sum(row[j][1] for row in rows)
            heavy+=int(bound<thresholds[j][known])
        least=min(least,heavy)
    assert 35+least>=required
    print(columns,height,least,'seventh-column terms require at least six primes',flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Enable assertions.')
    verify((8,7,5,3),'Erdos849PatternThree.json.gz',284)
    verify((8,7,6,5),'Erdos849PatternSixHost.json.gz',318)
    for height,required in [(1072,41),(1602,42)]:
        verify_seven((8,7,5,3),'Erdos849PatternThree.json.gz',height,required)
    for height,required in [(1689,41),(2235,42)]:
        verify_seven((8,7,6,5),'Erdos849PatternSixHost.json.gz',height,required)
