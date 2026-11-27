"""Second numerical verifier for the cap-15 graph and exceptional host rows.

Run python Erdos849SixteenAudit.py for both checks. The direct four-column
sieve on the 18 listed intervals is an independent input, as are the nine
published low-column classifications and the prime-power host congruence.
No routines from the cap-15 primary certificate are imported.
"""

import argparse
from functools import cache
from itertools import combinations
from math import comb, factorial, prod

from Erdos849FourteenAudit import (
    FIXED, SMALL, divisors_of_factorial, host_costs, last_true, primes_between,
    require, residue_image, root, singleton_minima,
)


CAP, LOW, HIGH = 15, 100, 500
# A small-base search includes the empty-host search.
HOSTS = {
    8: ((7,True),), 9: ((6,True),), 11: ((7,True),(10,True)),
    12: ((8,True),(11,True)), 13: ((12,True),), 14: ((12,True),(13,True)),
    15: ((4,False),(14,True)),
    16: tuple((j,False) for j in range(5,16)),
    17: tuple((j,False) for j in range(7,16)),
}
DIRECT = {
    (2,7,14,15):101, (3,5,7,11):104, (3,5,7,12):144, (3,5,7,13):134,
    (3,5,7,14):121, (3,5,7,15):179, (3,5,8,9):111, (3,5,14,15):101,
    (3,7,14,15):101, (4,5,7,11):104, (4,5,7,12):144, (4,5,7,13):134,
    (4,5,7,14):121, (5,6,7,11):104, (5,6,7,12):144, (5,6,7,13):134,
    (5,6,7,14):121, (5,7,14,15):101,
}


@cache
def partitions(total, parts, minimum=1):
    """Unordered positive bin sizes for assigning total items to <=parts bins."""
    if not total:
        return ((),)
    if not parts:
        return ()
    return tuple((first,)+rest for first in range(minimum,total+1)
                 for rest in partitions(total-first,parts-1,first))


def transfer_minimum(j,d,singles,lower,upper):
    # The product of the singleton cofactors in a bin of h is integral
    # and at least (n-d+1)^h/m. For h*j>=d its uniform lower bound scales
    # with a nonnegative power of a/(10^k). Other bins cost at least 1.
    costs = [1 if h*j<d else max(1,(lower**h+upper-1)//upper)
             for h in range(singles+1)]
    return min(prod(costs[h] for h in shape) for shape in partitions(singles,j))


@cache
def status(j,d,k):
    if (j,d) in FIXED:
        return "excluded"
    X = 10**k
    D = factorial(d)
    lower = root(D*X,d)-d+1
    upper = root(factorial(j)*X,j)+j
    if d>CAP:
        return "excluded" if lower>D else "empty"
    if d<2*j:
        costs = host_costs(X,j,d)
        least = singleton_minima(costs,D)
        large = sorted(c[0] for c in costs)
    else:
        least,large = [1]*(d+1),[1]*d
    permitted = set()
    for empty in range(d+1):
        if lower**empty>D:
            break
        singles = max(0,2*(d-empty)-CAP)
        group = transfer_minimum(j,d,singles,lower,upper)
        if lower**empty * max(group,least[singles]) > D:
            continue
        if empty:
            permitted.add("empty")
        elif prod(large[:singles]) > D:
            permitted.add("small")
        else:
            return "open"
    return "small" if "small" in permitted else "empty" if permitted else "excluded"


def covers(pattern,k,finite):
    for j,d in combinations(pattern,2):
        reason = status(j,d,k)
        if reason=="excluded":
            return True
        table = dict(HOSTS.get(d,())) if finite else {}
        if j in table and (reason=="empty" or (reason=="small" and table[j])):
            return True
    return False


def graph_check():
    for k,cut in ((LOW,18),(HIGH,16)):
        # C(n,t)/n^CAP increases with n for t>CAP, since its falling
        # factors (1-i/n) and n^(t-CAP) are increasing. The row n obeys
        # n^CAP >= a by the full-prime-power host property.
        N = root(10**k,CAP)
        require(N>=2*cut and comb(N,cut)>N**CAP,"column cutoff")
        count = direct = 0
        for pattern in combinations(range(2,cut),4):
            count += 1
            if covers(pattern,k,k==LOW):
                continue
            require(k==LOW and pattern in DIRECT,f"uncovered {pattern} at {k}")
            require(covers(pattern,DIRECT[pattern],True),f"uncovered direct tail {pattern}")
            direct += 1
        print(f"At 10^{k}, checked {count} graphs, {direct} direct gaps.",flush=True)


def centers(d,small,lo,hi):
    divisors = divisors_of_factorial(d)
    all_centers = {u for u in divisors if lo<=u<=hi}
    if small:
        # p-free u and v>=1 cover all b*p^e with b|d!, e>=1. Empty hosts
        # are already present. Intersect exactly with the binomial row range.
        for p in SMALL:
            if p>d:
                continue
            for u in divisors:
                if u%p==0:
                    continue
                center = u*p
                while center<lo:
                    center *= p
                while center<=hi:
                    all_centers.add(center)
                    center *= p
    return sorted(all_centers)


def check_rows(d,js,small):
    lo = last_true(lambda n: comb(n,d)<10**LOW)+1
    hi = last_true(lambda n: comb(n,d)<=10**HIGH)
    require(comb(lo-1,d)<10**LOW<=comb(lo,d)<=comb(hi,d)<=10**HIGH<comb(hi+1,d),
            "binomial row endpoints")
    filters = {}
    for j in js:
        filters[j] = sorted(((p,residue_image(p,j)) for p in primes_between(607,1300)),
                            key=lambda item:len(item[1])/item[0])
    rows = exact = 0
    last = lo-1
    for c in centers(d,small,lo-d+1,hi):
        end = min(hi,c+d-1)
        for n in range(max(last+1,c),end+1):
            rows += 1
            a = comb(n,d)
            for j in js:
                for p,image in filters[j]:
                    if a%p not in image:
                        break
                else:
                    exact += 1
                    m = last_true(lambda t: comb(t,j)<=a)
                    require(comb(m,j)!=a or m<2*j,f"collision {n,d,m,j}")
        last = max(last,end)
    print(f"d={d}, j={js}, small={small}: {rows} rows, {exact} exact inversions.",flush=True)
    return rows


if __name__=="__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only",choices=("graph","rows"))
    args = parser.parse_args()
    if args.only!="rows":
        graph_check()
    if args.only!="graph":
        jobs = [(d,tuple(j for j,sg in items if sg==small),small)
                for d,items in HOSTS.items() for small in (False,True)
                if any(sg==small for _,sg in items)]
        count = sum(check_rows(*job) for job in jobs)
        print(f"Verified {count} exceptional rows counted by search job.",flush=True)
