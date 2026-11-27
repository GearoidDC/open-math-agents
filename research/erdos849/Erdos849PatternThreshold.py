"""Exclude eleven large prime factors using the eight numerator hosts and CRT."""

from argparse import ArgumentParser
from concurrent.futures import ProcessPoolExecutor,as_completed
from itertools import combinations
from math import comb,prod
from time import monotonic

from Erdos849PatternCapTen import filters, row_root
from Erdos849PatternThree import PRIMES, floor_root, host_loss, root
from Erdos849PatternThreeCRT import row_in_column, wheel
from bisect import bisect_left,bisect_right

BUDGET,START,RATE = 35519,128,36


def host_end():
    low = root(8,START)-7
    constants = [max(prod(host_loss(S,p) for p in (2,3,5,7))
                     for S in combinations(range(8),j)) for j in (1,4)]
    assert constants == [117600,8467200]
    # low*T^(1/8)>C1*Q^3*T^(3/36), and
    # low^4*T^(4/8)>C4*Q^16*T^(16/36).
    k=START
    while (low**24*10**(k-START)<=(constants[0]*BUDGET**3)**24 or
           low**72*10**(k-START)<=(constants[1]*BUDGET**16)**18):
        k+=1
    return k


def plan():
    end=host_end()
    period=10*RATE
    places=(10*(end-START)+period-1)//period
    base=BUDGET**period*10**(period*places)
    fractional=[floor_root(base*10**v,period) for v in range(period)]
    groups=[]
    for i in range(10*START,10*end):
        whole,rem=divmod(i+1-10*START,period)
        q=1+fractional[rem]//10**(places-whole)
        powers={}
        for p in PRIMES:
            z=1
            while z*p<=q:
                z*=p
            powers[p]=z
        upper=420*q**11*prod(powers.values())
        slack=floor_root(upper**10//10**i,10)
        if not slack:
            continue
        # If p divides 420, its actual saturated power includes precisely
        # the permitted p-part of the common denominator.
        for p in (2,3,5,7):
            d=420
            while d%p==0:
                d//=p
                powers[p]*=p
        bases=tuple(sorted(powers,key=lambda p:p**3*powers[p],reverse=True))
        descriptor=tuple((p,powers[p]) for p in bases)
        if groups and groups[-1][1]==i and groups[-1][2]==descriptor:
            old=groups[-1]
            groups[-1]=(old[0],i+1,descriptor,max(old[3],slack))
        else:
            groups.append((i,i+1,descriptor,slack))
    return end,groups


def choices(bases,slack,width):
    # A search path records which maximal powers are attained and charges
    # at least p for every skipped prime p before reaching a terminal.
    def visit(i,loss,selected,modulus):
        k=len(selected)
        if k==6 or (k>=4 and 48*modulus>=width*8**k):
            yield selected
            return
        if i==len(bases):
            assert False,"insufficient saturated powers"
        p,z=bases[i]
        yield from visit(i+1,loss,selected+(z,),modulus*z)
        if loss*p<=slack:
            yield from visit(i+1,loss*p,selected,modulus)
    yield from visit(0,1,(),1)


def estimates(groups):
    stats={}
    for i,j,bases,slack in groups:
        assert prod(PRIMES[:20])>slack
        width=row_root(j)+9-row_root(i)
        for zs in choices(bases,slack,width):
            k=len(zs)
            cnt,expected=stats.get(k,(0,0))
            stats[k]=(cnt+1,expected+(width*8**k)//prod(zs))
    return stats


def stream(lo,hi,zs,cache):
    half=len(zs)//2
    left,right=zs[:half],zs[half:]
    m,rs=wheel(left)
    n,ss=wheel(right)
    if left not in cache:
        if len(cache)>=64:
            cache.clear()
        low,lr=divmod(lo,m)
        high,hr=divmod(hi,m)
        cache[left]=[(r,low+int(r<lr),high-int(r>hr)) for r in rs]
    inverse=pow(m,-1,n)
    ordered=sorted(s*inverse%n for s in ss)
    for r,low,high in cache[left]:
        if high<low:
            continue
        first=(low+r*inverse)%n
        span=high-low
        if span>=n-1:
            allowed=ordered
        else:
            j=bisect_left(ordered,first)
            last=first+span
            if last<n:
                allowed=ordered[j:bisect_right(ordered,last)]
            else:
                allowed=ordered[j:]+ordered[:bisect_right(ordered,last-n)]
        for t in allowed:
            for k in range(low+(t-first)%n,high+1,n):
                yield r+m*k


def run(group):
    i,j,bases,slack=group
    lo,hi=row_root(i),row_root(j)+8
    assert prod(PRIMES[:20])>slack
    cache={}
    checks=filters()
    totals=[0]*5
    for zs in choices(bases,slack,hi-lo+1):
        totals[len(zs)-4]+=1
        for n in stream(lo,hi,zs,cache):
            totals[3]+=1
            if not all(bits[n%p] for p,bits in checks):
                continue
            totals[4]+=1
            a=comb(n,8)
            assert not (row_in_column(a,5) and row_in_column(a,7)),(n,a)
    return totals


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("The certificate requires Python assertions.")
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--plan-only",action="store_true")
    parser.add_argument("--workers",type=int,default=6)
    args=parser.parse_args()
    t=monotonic()
    end,groups=plan()
    print(f"Tail 10^{end}, {len(groups)} ranges, {sum(j-i for i,j,_,_ in groups)} tenth-decades.",flush=True)
    if args.plan_only:
        print(estimates(groups),flush=True)
    else:
        from Erdos849PatternThreeCRT import candidate_rows
        for k in (4,5,6):
            test=(31,37,41,43,47,53)[:k]
            for lo,hi in [(30,700),(10**12,10**12+10**8)]:
                assert set(stream(lo,hi,test,{}))==candidate_rows(lo,hi,test)
        for i,j,_,_ in groups:
            for e in (i,j):
                a=40320**10*10**e
                n=row_root(e)
                assert n**80<=a<(n+1)**80
        groups.sort(key=lambda g:g[3],reverse=True)
        counts=[0]*5
        with ProcessPoolExecutor(args.workers) as pool:
            pending=[pool.submit(run,g) for g in groups]
            for finished,f in enumerate(as_completed(pending),1):
                counts=[x+y for x,y in zip(counts,f.result())]
                if finished%25==0:
                    print(f"Completed {finished}/{len(groups)} ranges.",flush=True)
        print(f"Four/five/six-modulus choices {counts[:3]}, {counts[3]} streamed row visits, "
              f"{counts[4]} exact membership tests, zero common values. "
              f"Elapsed {monotonic()-t:.1f} seconds.",flush=True)
