"""Test two small cubefree parts among eight consecutive terms in columns 7/8."""

from argparse import ArgumentParser
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
from math import gcd
from time import monotonic

from Erdos849HigherSquare import ceil_div
from Erdos849WiderOdd37 import in_seventh_column


def cube_root(n):
    if n < 2:
        return n
    x = 1 << ceil_div(n.bit_length(),3)
    while True:
        following = (2*x+n//(x*x))//3
        if following >= x:
            assert x**3 <= n < (x+1)**3
            return x
        x = following


def coefficient_pairs(primes):
    # Divide the two cubefree parts by their common factor before searching.
    pairs = [(1,1)]
    for p in primes:
        pairs = [(a*u,b*v) for a,b in pairs
                 for u,v in ((1,1),(p,1),(p*p,1),(1,p),(1,p*p))]
    return [(a,b) for a,b in pairs if a<=b]


def check_pair(job):
    a,b,bits = job
    bound = 1 << bits
    pairs = set()

    def test(x,y):
        left, right = a*x**3,b*y**3
        gap = abs(left-right)
        if x>0 and 1<=gap<=7:
            pairs.add((min(left,right),max(left,right)))

    for y in range(1,29):
        lo = cube_root(max(0,b*y**3-7)//a)
        hi = cube_root((b*y**3+7)//a)
        for x in range(lo,hi+1):
            test(x,y)
    if (a,b)==(1,1):
        return 0,pairs

    denominator = 1 << (3*bits+2)
    numerator = cube_root(b*denominator**3//a)
    prev_p,p,prev_q,q = 0,1,1,0
    steps = 0
    while denominator:
        digit,remainder = divmod(numerator,denominator)
        # A previous convergent sufficiently close to the target cubic
        # irrational must have a large following partial quotient.
        if q>28 and q < 8*(digit+2):
            test(p,q)
        prev_p,p = p,digit*p+prev_p
        prev_q,q = q,digit*q+prev_q
        steps+=1
        if q>=bound:
            break
        numerator,denominator = denominator,remainder
    else:
        if q>28:
            test(p,q)
    return steps,pairs


def main(decade,primes,workers):
    started = monotonic()
    bits = 2+ceil_div(10*decade,72)
    assert 3*(24*bits-24)>=10*decade
    coefficients = coefficient_pairs(primes)
    assert len(coefficients)==(5**len(primes)+1)//2
    assert all(gcd(a,b)==1 for a,b in coefficients)
    primitive = set()
    steps = 0
    jobs = ((a,b,bits) for a,b in coefficients)
    with ProcessPoolExecutor(workers) as executor:
        for count,found in executor.map(check_pair,jobs,chunksize=12):
            steps+=count
            primitive.update(found)
    pairs=set()
    for low,high in primitive:
        for scale in range(1,7//(high-low)+1):
            pairs.add((scale*low,scale*high))
    # Factor every small endpoint independently and reproduce the nearby pairs.
    control_limit = 20000
    admissible = set()
    for n in range(1,control_limit+1):
        core = n
        for prime in primes:
            while core%prime==0:
                core//=prime
        if cube_root(core)**3==core:
            admissible.add(n)
    direct = {(n,n+g) for n in admissible for g in range(1,8) if n+g in admissible}
    if decade >= 40:
        assert direct == {(low,high) for low,high in pairs if high<=control_limit}
    rows={n for low,high in pairs for n in range(max(16,high),low+8)}
    assert not any(in_seventh_column(n) for n in rows)
    print(f"Support through {primes[-1]}, height 10^{decade}, {len(coefficients):,} ratios, "
          f"{steps:,} continued-fraction steps, {len(primitive):,} unscaled pairs, "
          f"{len(pairs):,} scaled pairs, {len(rows):,} admissible rows; "
          f"maximum row {max(rows)}, {len(direct):,} direct controls, zero collisions, "
          f"{monotonic()-started:.1f} s.",flush=True)


if __name__ == "__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--support",type=int,choices=(7,11,13),default=7)
    parser.add_argument("--decade",type=int,default=53592)
    parser.add_argument("--workers",type=int,default=4)
    args=parser.parse_args()
    if args.decade<1 or args.workers<1 or not __debug__:
        parser.error("Use positive parameters and enable assertions.")
    main(args.decade,tuple(p for p in (2,3,5,7,11,13) if p<=args.support),args.workers)
