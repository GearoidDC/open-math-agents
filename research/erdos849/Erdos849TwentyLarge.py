"""An independent height cutoff for twenty distinct prime factors in a five-row value."""

from fractions import Fraction
from functools import lru_cache
from itertools import combinations
import gzip
import json
from math import factorial, lcm

from Erdos849InterpolatedPowers import DATA, check, endpoint, floor_root, tangent
from Erdos849SingletonInterpolation import prime_bound, BASES, denominator


@lru_cache(None)
def divisors(k):
    values = [1]
    for p in (2,3,5,7,11,13,17,19):
        f, n = 0, k
        while n:
            n //= p
            f += n
        if f:
            values = [v*p**i for v in values for i in range(f+1)]
    return values


@lru_cache(None)
def ends(k,decade):
    r = floor_root(factorial(k)*10**decade,k)
    return r-k+1,r+k


def disconnected(j,d,decade):
    """Check all possible component size partitions of the host graph."""
    need = d+j-19
    if need<=1:
        return False
    lj,uj = ends(j,decade)
    ld,ud = ends(d,decade)
    mj,md = lcm(*range(1,j+1)),lcm(*range(1,d+1))
    if lj<=mj or ld<=md:
        return False
    allowed = []
    for h in range(1,d+1):
        for q in range(1,j+1):
            bj = min(factorial(j),mj**q)
            bd = min(factorial(d),md**h)
            if h*j>=q*d and ld**h>bd*uj**q:
                continue
            if q*d>=h*j and lj**q>bj*ud**h:
                continue
            if h*j==q*d and (h,q)!=(d,j):
                if not any((t*ld**h+uj**q-1)//uj**q <= min(bd,t*ud**h//lj**q)
                           for t in divisors(j) if t<=bj):
                    continue
            allowed.append((h,q))
    @lru_cache(None)
    def possible(h,q,n):
        if not h or not q:
            return h==q==0 and n<=0
        if min(h,q)<n:
            return False
        return any(possible(h-a,q-b,n-1) for a,b in allowed if a<=h and b<=q)
    return not possible(d,j,need)


@lru_cache(None)
def pair_constants(j,d):
    with gzip.open(DATA,"rt",encoding="ascii") as handle:
        data = json.load(handle)
    branches = []
    for s in range(d):
        for r in range(j):
            cert = data.get(f"{j},{d},{r},{s}",tangent(j,d,r,s))
            h,w,H,_ = check(j,d,r,s,cert)
            L = lcm(denominator(d,s),denominator(j,r))
            ordinary = floor_root(H,h)+1
            C = max([ordinary]+[prime_bound(j,d,r,s,L,h,H,cert[1],p) for p in BASES])
            branches.append((C,Fraction(w,j*d*h)))
    return branches


@lru_cache(None)
def forced(k,j,d,decade):
    """Each of the k terms must host strictly more than floor(19/k) powers."""
    t = 19//k
    B = lcm(*range(1,k+1))
    lower = endpoint(k)-k+1
    # A common envelope handles products whose powers use different branches.
    for C,alpha in pair_constants(j,d):
        g = Fraction(1,k)-t*alpha
        if g<0 or (B*C**t)**g.denominator >= lower**g.denominator*10**((decade-128)*g.numerator):
            return False
    return True


def main(decade):
    assert decade>=128
    cutoff = next(k for k in range(20,23) if ends(k,decade)[1]**19<10**decade)
    classified = {(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,6),(4,6),(4,8)}
    forbidden = classified | {(j,d) for d in range(3,cutoff) for j in range(2,d)
                              if disconnected(j,d,decade)}
    remaining = []
    for pattern in combinations(range(2,cutoff),4):
        if any(pair in forbidden for pair in combinations(pattern,2)):
            continue
        # Any available certified pair may be used to test any column in the tuple.
        if any(forced(k,j,d,decade) for j,d in combinations(pattern,2)
               if 7<=j<d<=17 for k in pattern):
            continue
        remaining.append(pattern)
    return cutoff,remaining


if __name__=="__main__":
    import sys
    decade = int(sys.argv[1]) if len(sys.argv)>1 else 310
    cutoff,remaining=main(decade)
    print(f"10^{decade}, direct cutoff {cutoff}, remaining patterns {len(remaining)}: {remaining[:20]}")
    assert not remaining
