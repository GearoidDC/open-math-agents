"""Classify the missing-cell case at the published lower bound, with integers."""

from fractions import Fraction
from math import isqrt, prod

from Erdos849ThreeEightCells import (
    CUBIC, QUARTIC, SCALES, candidates, disk_bounds, row_floor
)


def upper_for_integer(bounds):
    def small(limit):
        return sum(x * Fraction(1,limit)**i for i,x in enumerate(bounds,1)) < 1
    lo, hi = 0, 1
    while not small(hi):
        lo, hi = hi, 2*hi
    while hi-lo > 1:
        mid=(lo+hi)//2
        if small(mid):
            hi=mid
        else:
            lo=mid
    return hi-1


def primes_through(limit):
    return [n for n in range(11,limit+1) if all(n%d for d in range(2,isqrt(n)+1))]


def image(i,r,scale,cert,p):
    roots = {}
    for x in range(p):
        roots.setdefault(6720*(x**3-x)%p,[]).append(x)
    seen = set()
    for Y in {(m-3)*(m-4)%p for m in range(p)}:
        y=(Y-r)%p
        for x in roots.get(prod(Y-q for q in QUARTIC)%p,[]):
            if y:
                z=scale*prod(x-v for t,v in enumerate(CUBIC) if t!=i)*pow(y,-1,p)%p
            elif x != CUBIC[i]%p:
                z=scale*prod(Y-q for q in QUARTIC if q!=r)*pow(6720*(x-CUBIC[i]),-1,p)%p
            else:
                continue
            seen.add(sum(c*pow(x,u,p)*pow(y,v,p)*pow(z,w,p) for u,v,w,c in cert)%p)
    return seen


def image_control(i,r,scale,cert,p):
    seen=set()
    for m in range(p):
        Y=(m-3)*(m-4)%p
        y=(Y-r)%p
        for x in range(p):
            for z in range(p):
                if (y*z-scale*prod(x-v for t,v in enumerate(CUBIC) if t!=i))%p:
                    continue
                if (6720*(x-CUBIC[i])*z-scale*prod(Y-q for q in QUARTIC if q!=r))%p:
                    continue
                seen.add(sum(c*pow(x,u,p)*pow(y,v,p)*pow(z,w,p) for u,v,w,c in cert)%p)
    return seen


def interval_sieve(masks,limit):
    masks.sort(key=lambda pair: Fraction(len(pair[1]),pair[0]))
    # Repeat each p-bit mask once, then align it for each consecutive
    # integer interval. Each set bit represents precisely one survivor.
    block=min(1<<20,2*limit+1)
    periodic=[]
    for p,good in masks:
        period=sum(1<<r for r in good)
        copies=(block+p-1)//p+1
        repeat=((1<<(p*copies))-1)//((1<<p)-1)
        periodic.append((p,period*repeat))
    survivors=[]
    for first in range(-limit,limit+1,block):
        live=(1<<min(block,limit-first+1))-1
        for p,mask in periodic:
            live &= mask>>(first%p)
            if not live:
                break
        while live:
            bit=live & -live
            value=first+bit.bit_length()-1
            if value:
                survivors.append(value)
            live-=bit
    return survivors


def main():
    if not __debug__:
        raise RuntimeError("Enable assertions.")
    for i in range(3):
        for r,scale in zip(QUARTIC,SCALES):
            base=row_floor(60,r)
            degree,polys,cert=next(obj for obj in candidates(i,r,scale,5) if obj[0]==5)
            bounds=disk_bounds(polys,base)
            assert bounds
            limit=upper_for_integer(bounds)
            masks=[(p,image(i,r,scale,cert,p)) for p in primes_through(191)]
            for p,good in masks[:2]:
                assert good==image_control(i,r,scale,cert,p)
            # The genuine point over a=1 must survive every local image.
            y=20-r
            z=Fraction(scale*prod(2-v for t,v in enumerate(CUBIC) if t!=i),y)
            value=sum(c*2**a*y**b*z**d for a,b,d,c in cert)
            assert value.denominator==1
            assert all(int(value)%p in good for p,good in masks)
            control=masks[:3]
            direct=[n for n in range(-2000,2001) if n and all(n%p in good for p,good in control)]
            assert direct and interval_sieve(control,2000)==direct
            values=interval_sieve(masks,limit)
            print(i,r,limit,len(values),flush=True)
            assert values==[]


if __name__=='__main__':
    main()
