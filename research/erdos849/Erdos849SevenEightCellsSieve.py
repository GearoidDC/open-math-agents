"""Check missing intersections of columns eight and seven at large heights."""

from fractions import Fraction
from pathlib import Path
import json
from Erdos849SaturatedCells import integer_valued, normal_form, slope_bounds
from Erdos849CellSieve import primes, range_sieve
from Erdos849SevenCellsSieve import images


def analyze(i,j,coefficients,height,limit=283):
    assert 0<=i<4 and 0<=j<7 and coefficients and all(type(c)==int for c in coefficients)
    poly=normal_form(8,7,i,j,coefficients)
    integer_valued({key:c for key,c in poly.items() if key[1]>=0},8,7,j)
    rem={key:c for key,c in poly.items() if key[1]<0}
    base,lo,hi=slope_bounds(8,7,height)
    weight=lambda key:7*key[0]+4*key[1]
    assert rem and all(weight(key)<0 for key in rem)
    sizes={key:abs(c)*hi**key[0]*Fraction(base)**weight(key) for key,c in rem.items()}
    total=sum(sizes.values())
    cap=total.numerator//total.denominator
    lead=max(rem,key=weight)
    minimum=abs(rem[lead])*lo**lead[0]*Fraction(base)**weight(lead)
    sign=0
    if minimum>total-sizes[lead]:
        sign=1 if rem[lead]>0 else -1
    if cap==0 and sign:
        return cap,[]
    masks=[(p,images(8,i,j,coefficients,poly,p,control=p<53))
           for p in primes(limit) if p>max(len(coefficients),7)]
    survivors=range_sieve(cap,masks)
    if sign:
        survivors=[s for s in survivors if sign*s>0]
    return cap,survivors


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Enable assertions.')
    records=json.loads(Path(__file__).with_suffix('.json').read_text())
    assert set(records)=={f'{i},{j}' for i in range(4) for j in range(7)}
    for key,(height,coefficients) in sorted(records.items()):
        i,j=map(int,key.split(','))
        assert height==136
        cap,left=analyze(i,j,coefficients,height)
        assert not left
        print(key,height,cap,flush=True)
