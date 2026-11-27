"""Exclude at most ten prime divisors above 100 for both eight-column patterns.

The four-column archives bound every full p-power by p^v_p(420) times
Y=Q*(a/10^128)^(1/36). The default Q=35519 also covers the Q=34800 archive.
Above the stated final height the inequality a<=420*Y^35 is impossible.
Below it, let q bound Y on one tenth-decade. Then the coefficient is at
most U=420*q^10 times the product of the largest powers of primes under
100 that fit in q. If a prime p>7 does not attain its maximal power,
the actual product loses a factor of at least p from U. The integer
slack below compares these losses to the lower endpoint of the band.

We select primes so that six maximal powers must occur. Each divides
one of the eight numerator factors, so its row residue is in 0,...,7.
The CRT join streams the eligible rows. Modulo each checking prime the
row's eighth coefficient must be in both the fifth- and seventh-column
images, and the final checks use exact integer binomial coefficients.
Both four-column patterns contain those three columns.

Run with --plan-only for coverage counts or --workers N for a full replay.
"""

from argparse import ArgumentParser
from bisect import bisect_left,bisect_right
from concurrent.futures import ProcessPoolExecutor,as_completed
from functools import lru_cache
from itertools import combinations
from math import comb, factorial, isqrt, prod
from time import monotonic

from Erdos849PatternThree import PRIMES, floor_root
from Erdos849PatternThreeCRT import row_in_column,wheel


def fifth(a):
    x = 1<<((a.bit_length()+4)//5)
    while True:
        y = (4*x+a//x**4)//5
        if y>=x:
            return x
        x = y


def row_root(i):
    a = factorial(8)**10*10**i
    for _ in range(4):
        a = isqrt(a)
    return fifth(a)


def plan(budget):
    cap,rate,decade,large = 35,36,128,10
    end = decade
    while (420*budget**cap)**rate>=10**(decade*cap+end*(rate-cap)):
        end+=1
    period = 10*rate
    places = (10*(end-decade)+period-1)//period
    base = budget**period*10**(places*period)
    fractional = [floor_root(base*10**v,period) for v in range(period)]
    groups=[]
    count=0
    for i in range(10*decade,10*end):
        whole,rem=divmod(i+1-10*decade,period)
        q=1+fractional[rem]//10**(places-whole)
        powers={}
        for p in PRIMES:
            z=1
            while z*p<=q:
                z*=p
            powers[p]=z
        top=420*q**large*prod(powers.values())
        # If the product of losses is greater than slack, the row is impossible.
        slack=floor_root(top**10//10**i,10)
        if not slack:
            continue
        count+=1
        required=6
        # Within a set of z primes, a row having fewer than six saturated
        # powers would lose at least the z-5 smallest prime bases.
        eligible=tuple(p for p in PRIMES if p>7)
        for size in range(required,len(eligible)+1):
            subset=eligible[-size:]
            if prod(subset[:size-required+1])>slack:
                break
        else:
            raise AssertionError(("no saturation",i))
        # Prefer larger powers if the same minimum number of successes is certified.
        by_power=sorted(eligible,key=lambda p:powers[p],reverse=True)
        best=tuple(sorted(by_power[:size]))
        if prod(best[:size-required+1])>slack:
            subset=best
        descriptor=tuple(sorted((powers[p] for p in subset),reverse=True))
        if groups and groups[-1][1]==i and groups[-1][2]==descriptor:
            groups[-1]=(groups[-1][0],i+1,descriptor)
        else:
            groups.append((i,i+1,descriptor))
    return count,end,groups


def join(lo,hi,moduli,left_cache):
    left,right=moduli[:3],moduli[3:]
    m,ls=wheel(left)
    if left not in left_cache:
        low,low_rem=divmod(lo,m)
        high,high_rem=divmod(hi,m)
        left_cache[left]=[(x,low+int(x<low_rem),high-int(x>high_rem)) for x in ls]
    n,rs=wheel(right)
    inverse=pow(m,-1,n)
    ordered=sorted(x*inverse%n for x in rs)
    for x,lower,upper in left_cache[left]:
        if lower>upper:
            continue
        first=(lower+x*inverse)%n
        length=upper-lower
        if length>=n-1:
            allowed=ordered
        else:
            last=first+length
            lower_index=bisect_left(ordered,first)
            if last<n:
                allowed=ordered[lower_index:bisect_right(ordered,last)]
            else:
                allowed=ordered[lower_index:]+ordered[:bisect_right(ordered,last-n)]
        for y in allowed:
            start=lower+(y-first)%n
            for k in range(start,upper+1,n):
                yield x+m*k


@lru_cache(None)
def filters():
    # For p>8 the binomial in each column is a polynomial modulo p.
    checks=[]
    for p in (101,103,107,109,113,127,131,137,139,149,151,157,163):
        image={comb(x,5)%p for x in range(p)} & {comb(x,7)%p for x in range(p)}
        accepted=bytes(comb(x,8)%p in image for x in range(p))
        checks.append((p,accepted))
    return sorted(checks,key=lambda item:sum(item[1])/item[0])


def run_group(group):
    i,j,moduli=group
    lo,hi=row_root(i),row_root(j)+8
    checks=filters()
    emitted=exact=0
    # Cache only the current left wheel; combinations orders equal
    # initial triples consecutively, so a single entry is sufficient.
    cache={}
    previous=None
    for required in combinations(moduli,6):
        if required[:3]!=previous:
            cache.clear()
            previous=required[:3]
        for n in join(lo,hi,required,cache):
            emitted+=1
            if not all(bits[n%p] for p,bits in checks):
                continue
            exact+=1
            a=comb(n,8)
            assert not (row_in_column(a,5) and row_in_column(a,7)),(n,a)
    return emitted,exact


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--budget",type=int,default=35519,choices=(34800,35519))
    parser.add_argument("--workers",type=int,default=4)
    parser.add_argument("--plan-only",action="store_true")
    args=parser.parse_args()
    start=monotonic()
    n,end,groups=plan(args.budget)
    total=sum(comb(len(moduli),6) for _,_,moduli in groups)
    print(f"Budget {args.budget}, continuous tail 10^{end}, {n} difficult bands, "
          f"{len(groups)} ranges, {total} six-prime choices.",flush=True)
    if not args.plan_only:
        moduli=(31,37,41,43,47,53)
        lo,hi=10**12,10**12+10**8
        from Erdos849PatternThreeCRT import candidate_rows
        assert set(join(lo,hi,moduli,{}))==candidate_rows(lo,hi,moduli)
        assert all(pow(row_root(i),80)<=factorial(8)**10*10**i<(row_root(i)+1)**80
                   for i in {k for start_i,end_i,_ in groups for k in (start_i,end_i)})
        groups.sort(key=lambda g:comb(len(g[2]),6),reverse=True)
        emitted=exact=done=0
        with ProcessPoolExecutor(args.workers) as pool:
            futures={pool.submit(run_group,g):comb(len(g[2]),6) for g in groups}
            for f in as_completed(futures):
                x,y=f.result()
                emitted+=x
                exact+=y
                done+=futures[f]
                if done//50000!=(done-futures[f])//50000:
                    print(f"{done}/{total} prime choices completed.",flush=True)
        print(f"{emitted} streamed CRT row visits, {exact} after modular checks, "
              f"zero common values. Elapsed {monotonic()-start:.1f} s.",flush=True)
