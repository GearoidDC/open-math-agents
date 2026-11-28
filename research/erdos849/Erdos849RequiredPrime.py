"""Exclude nonzero fibers at 53 using real interval bounds on auxiliary polynomials."""

from itertools import product
import json
from math import factorial, prod
from pathlib import Path

from Erdos849LocalInterpolation import floor_root
from Erdos849ResidueDisks import fibers, verify_vanishing


def check_signs(columns,height,lower_height,degrees,polys):
    for flip in product(*([(0,1) if k%2==0 else (0,) for k in columns])):
        signs = [(-1)**sum(e*b for e,b in zip(es,flip)) for es in degrees]
        signed = [[x*c for x,c in zip(signs,cs)] for cs in polys]
        intervals = [(10**lower_height,10**height,0)]
        while intervals:
            left,right,depth = intervals.pop()
            lower = [floor_root(factorial(k)*left,k)-k for k in columns]
            upper = [floor_root(factorial(k)*right,k)+k for k in columns]
            assert min(lower)>0
            lo = [prod(x**e for x,e in zip(lower,es)) for es in degrees]
            hi = [prod(x**e for x,e in zip(upper,es)) for es in degrees]
            for cs in signed:
                low = sum(c*(a if c>=0 else b) for c,a,b in zip(cs,lo,hi))
                high = sum(c*(b if c>=0 else a) for c,a,b in zip(cs,lo,hi))
                if low>0 or high<0:
                    break
            else:
                assert depth<64 and left<right
                mid = floor_root(left*right,2)
                assert left<=mid<right
                intervals.extend(((left,mid,depth+1),(mid+1,right,depth+1)))


def check_record(columns,prime,height,low,record):
    offsets,free,precision,degrees,polys = record
    verify_vanishing(columns,prime,height,offsets,free,precision,degrees,polys)
    check_signs(columns,height,low,degrees,polys)


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    cols,p,low,h,records = json.loads(Path(__file__).with_suffix('.json').read_bytes())
    assert cols==[8,7,6,5] and (p,low,h)==(53,146,170)
    expected = {s for v,points in fibers(cols,p,True).items() if v for s in points}
    assert len(records)==len(expected) and expected=={tuple(r[0]) for r in records}
    for record in records:
        check_record(cols,p,h,low,record)
    print('Every common value in the interval is divisible by',p)
