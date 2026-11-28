"""Independent seed and modular-index audit for the 37-smooth square-class test."""

from argparse import ArgumentParser
from concurrent.futures import ProcessPoolExecutor, as_completed
from functools import cache
from itertools import combinations
from math import comb, isqrt
from time import monotonic

from Erdos849PellSmall import primitive_solutions
from Erdos849SquareClassAudit import images, in_seventh_column
from Erdos849WiderOdd import kernels
from Erdos849WiderOdd37 import fundamental_data


@cache
def modular_images():
    return tuple(images())


def independent_unit(d):
    """Use the actual convergent norm with a modular prefilter."""
    root = isqrt(d)
    m, den, digit = 0, 1, root
    x_old, x, y_old, y = 1, root, 0, 1
    while True:
        u, v = x%65521, y%65521
        if (u*u-d*v*v)%65521==1 and x*x-d*y*y==1:
            return x,y
        m = digit*den-m
        den = (d-m*m)//den
        digit = (root+m)//den
        x_old,x = x,digit*x+x_old
        y_old,y = y,digit*y+y_old


def independent_seeds(d, unit):
    """Run the unimodular-basis algorithm even for the large radicands."""
    _,v = unit
    result = {g:{(g,0)} for g in range(1,8)}
    for x,y,h in primitive_solutions(d,range(1,8),7*v):
        if y>=h*v:
            continue
        for gap in range(h,8,h):
            factor = gap//h
            result[gap].add((factor*x,factor*y))
    return result


def audit_kernel(d):
    unit = independent_unit(d)
    reference_unit,reference_seeds,_ = fundamental_data(d)
    assert unit==reference_unit
    seeds = independent_seeds(d,unit)
    assert all(seeds[g]==set(reference_seeds[g]) for g in range(1,8))
    u,v=unit
    # 1,340,000 exceeds the primary 1,337,504 bound on the growth exponent.
    end=1+1340000//(u.bit_length()-1)
    group_count=0
    for left,right in combinations(range(8),2):
        offset_sum=left+right
        for x,y in seeds[right-left]:
            group_count+=1
            flags=bytearray(b"\x01")*end
            # Parity of x,y is periodic modulo two under the unit matrix.
            a,b=x%2,y%2
            start=a,b
            parity=[]
            while True:
                parity.append(b==0 and (a+offset_sum)%2==0)
                a,b=(u*a+d*v*b)%2,(v*a+u*b)%2
                if (a,b)==start:
                    break
                assert len(parity)<6
            for t,ok in enumerate(parity):
                if not ok and t<end:
                    flags[t::len(parity)] = bytes((end-1-t)//len(parity)+1)
            # Tiny true rows can be recognized before the prime sieve.
            a,b=x,y
            index=0
            while index<end and a+offset_sum<32:
                flags[index]=0
                a,b=u*a+d*v*b,v*a+u*b
                index+=1
            doubled=x+offset_sum
            next_doubled=u*x+d*v*y+offset_sum
            for prime,permitted in modular_images():
                if flags.find(1)==-1:
                    break
                first,second = doubled%prime,next_doubled%prime
                a,b=first,second
                trace=(2*u)%prime
                constant=(2-trace)*offset_sum%prime
                inv_two=(prime+1)//2
                admissible=[]
                while True:
                    admissible.append(permitted[a*inv_two%prime])
                    a,b=b,(trace*b-a+constant)%prime
                    if (a,b)==(first,second):
                        break
                    assert len(admissible)<=2*prime
                length=len(admissible)
                for t,ok in enumerate(admissible):
                    if not ok and t<end:
                        flags[t::length]=bytes((end-1-t)//length+1)
            assert flags.find(1)==-1,(d,left,right)
    return group_count


def main(workers):
    if not __debug__:
        raise RuntimeError("This audit requires Python assertions.")
    started=monotonic()
    assert 24*(1340000-2)>10*3210000+3*16
    # D=1 gives x<=25 and n<=19 by factoring the difference of squares.
    assert not any(in_seventh_column(comb(n,8)) for n in range(16,20))
    with ProcessPoolExecutor(workers) as pool:
        jobs=[pool.submit(audit_kernel,d) for d in reversed(kernels(37)[1:])]
        total=0
        for count,job in enumerate(as_completed(jobs),1):
            total+=job.result()
            if count%1000==0:
                print(f"Audited {count}/{len(jobs)} nonsquare kernels.",flush=True)
    assert total==142200
    print(f"Independently audited {total:,} Pell orbits through 10^3210000. "
          f"No admissible index survived. Elapsed {monotonic()-started:.1f} s.",flush=True)


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--workers",type=int,default=6)
    args=parser.parse_args()
    if args.workers<1:
        parser.error("--workers must be positive")
    main(args.workers)
