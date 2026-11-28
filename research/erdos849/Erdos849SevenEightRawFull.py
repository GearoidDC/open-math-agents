"""Verify that every individual term-pair of columns seven and eight is occupied."""

import json
from fractions import Fraction
from math import comb
from pathlib import Path

from Erdos849RawCellTools import integer_valued,normal_form,slope_bounds

def reflected(cs):
    return [sum((-1)**t*comb(t-1,r-1)*cs[t-1] for t in range(r,len(cs)+1))
            for r in range(1,len(cs)+1)]


def bound(poly,height):
    B,lo,hi=slope_bounds(7,8,height);B=Fraction(B)
    rem={key:c for key,c in poly.items() if key[1]<0}
    def weight(key):return 8*key[0]+7*key[1]
    lead=max(rem,key=weight)
    assert weight(lead)<0 and len({weight(k) for k in rem})==len(rem)
    vals={k:abs(c)*hi**k[0]*B**weight(k) for k,c in rem.items()}
    total=sum(vals.values())
    lower=abs(rem[lead])*lo**lead[0]*B**weight(lead)
    return total<1 and lower>total-vals[lead]


def verify(i,j,height,cs):
    assert 0<=i<7 and 0<=j<8 and cs and all(type(c) is int for c in cs)
    poly=normal_form(7,8,i,j,cs)
    integer_valued({k:c for k,c in poly.items() if k[1]>=0})
    assert bound(poly,height),(i,j,height)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Enable assertions.')
    d=json.loads(Path(__file__).with_suffix('.json').read_text());data=d['cells'];height=d['height']
    cutoffs=d.get('cell_heights',{k:height for k in data})
    assert set(data)=={f'{i},{j}' for i in range(7) for j in range(4)}
    assert set(cutoffs)==set(data) and max(cutoffs.values())==height
    for key,cs in data.items():
        i,j=map(int,key.split(','));cut=cutoffs[key]
        verify(i,j,cut,cs);verify(i,7-j,cut,reflected(cs))
        print(i,j,7-j,cut,flush=True)
    print('Occupied individual cells:',56,'at height',height,flush=True)
