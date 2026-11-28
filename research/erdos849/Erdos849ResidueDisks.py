"""Verify small auxiliary polynomials on residue classes of four simultaneous binomials."""

import json
from itertools import product
from math import comb, factorial, prod
from pathlib import Path

from Erdos849LocalInterpolation import floor_root
from Erdos849RawCellTools import derivative, falling


def fibers(columns, prime, reflect):
    images = []
    for k in columns:
        by_value = {}
        for x in range(prime):
            if reflect and k%2==0 and (k-1-x)%prime < x:
                continue
            by_value.setdefault(comb(x,k)%prime,[]).append(x)
        images.append(by_value)
    return {v:list(product(*(image[v] for image in images)))
            for v in set.intersection(*(set(image) for image in images))}


def valuations(columns, offsets, free, prime, precision, degrees):
    q = prime**precision
    inverse = pow(factorial(columns[free]),-1,q)
    for t in range(precision):
        x = offsets[free]+prime*t
        a = falling(x,columns[free])*inverse%q
        row = []
        for i,(k,r) in enumerate(zip(columns,offsets)):
            if i==free:
                row.append(x)
                continue
            assert derivative(r,k)%prime
            n = r
            digits = 1
            while digits < precision:
                digits = min(2*digits,precision)
                m = prime**digits
                n = (n-(falling(n,k)-a*factorial(k))*pow(derivative(n,k),-1,m))%m
            assert n%prime == r and (falling(n,k)-a*factorial(k))%q == 0
            row.append(n)
        yield [prod(pow(x,e,q) for x,e in zip(row,es))%q for es in degrees]


def verify_vanishing(columns,prime,height,offsets,free,precision,degrees,polys):
    assert 0<=free<len(columns) and precision>=1 and polys and degrees
    assert all(len(es)==len(columns) and all(0<=e<k for e,k in zip(es,columns))
               for es in degrees)
    q = prime**precision
    upper = [floor_root(factorial(k)*10**height,k)+k for k in columns]
    sizes = [prod(n**e for n,e in zip(upper,es)) for es in degrees]
    for cs in polys:
        assert len(cs)==len(degrees) and all(type(c) is int for c in cs)
        assert sum(abs(c)*v for c,v in zip(cs,sizes))<q
    for row in valuations(columns,offsets,free,prime,precision,degrees):
        assert all(sum(c*x for c,x in zip(cs,row))%q==0 for cs in polys)


def verify(columns,prime,height,record):
    offsets,free,precision,second,degrees,polys = record
    verify_vanishing(columns,prime,height,offsets,free,precision,degrees,polys)
    assert second in {11,13,17,19,23}
    for points in fibers(columns,second,False).values():
        for s in points:
            row = [prod(pow(x,e,second) for x,e in zip(s,es))%second for es in degrees]
            assert any(sum(c*x for c,x in zip(cs,row))%second for cs in polys)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    data = json.loads(Path(__file__).with_suffix('.json').read_bytes())
    cols,p,h,records = data
    assert cols==[8,7,6,5] and p==113 and h==175
    expected = {s for v,points in fibers(cols,p,True).items() if v not in (0,1) for s in points}
    assert expected=={tuple(r[0]) for r in records} and len(records)==len(expected)
    for record in records:
        verify(cols,p,h,record)
    print('Verified disks:',len(records),'height:',h,'allowed coefficient residues:',[0,1])
