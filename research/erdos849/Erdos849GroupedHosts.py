"""Verify the balanced-bin exclusion for Erdős 849 with exact integer arithmetic.

Run: python Erdos849GroupedHosts.py
Optional: --cap 14 --power 100, or --large-singletons / --no-empty to
explore what follows if additional exceptional-row claims are supplied.
The default uses neither of those hypotheses.
"""

from argparse import ArgumentParser
from functools import cache
from itertools import combinations
from math import comb, factorial, gcd
from Erdos849ThirteenGraph import PUBLISHED, divisors_of_factorial, root


@cache
def scales(k, power):
    return root(factorial(k)*10**power, k)


@cache
def costs(j,d,power,large):
    Rj, Rd = scales(j,power), scales(d,power)
    possible = divisors_of_factorial(d)
    small = [] if large else [p for p in (2,3,5,7,11,13) if p<=d]
    rows = []
    for s in range(d):
        row = []
        for p in [0,*small]:
            bound = factorial(d)+1
            for r in range(j):
                A = factorial(j)*factorial(s)*factorial(d-1-s)
                B = factorial(d)*factorial(r)*factorial(j-1-r)
                left, right = A*(Rd+d-s), B*(Rj+j-r)
                same = (d-1-s-j+1+r)%2 == 0
                if same and B*(Rj-r) <= left:
                    bound=1
                    break
                g=gcd(A,B)
                while p and g%p == 0:
                    g//=p
                H=max(left,right) if same else left+right
                assert H%g==0
                H//=g
                bound=min(bound,next((v for v in possible if v*v*H >= (Rd-s)**2),factorial(d)+1))
            row.append(bound)
        rows.append(row)
    return rows


@cache
def weight_minimum(j,d,singletons,power,large):
    # The p^2 divisibility argument is recorded in Erdos849FourteenBound.py.
    # Here prime bases <=d can occur at most once each, larger bases can repeat.
    if singletons==0 or d>=2*j:
        return 1
    best={(0,0):1}
    for row in costs(j,d,power,large):
        out=dict(best)
        for (n,mask),product in best.items():
            if n>=singletons:
                continue
            for i,v in enumerate(row):
                bit=0 if i==0 else 1<<(i-1)
                if mask&bit:
                    continue
                key=(n+1,mask|bit)
                out[key]=min(out.get(key,product*v),product*v)
        best=out
    return min(v for (n,_),v in best.items() if n==singletons)


def grouped_bound(j,d,S,power):
    """A numerator/denominator lower bound for the singleton cofactor product."""
    L, U = scales(d,power)-d+1, scales(j,power)+j
    q,r=divmod(S,j)
    top,bottom=1,1
    # Each singleton n-s=b_s P_s has a distinct prime base. Assign P_s to
    # a factor m-i it divides in the other row. Such a factor exists by the
    # maximal-valuation host lemma, even for prime bases <=j. A bin of h
    # hosts gives product b_s >= max(1,(n-d+1)^h/m). The logarithm of this
    # last function is convex in h, so distributing S hosts as evenly as
    # possible minimizes the product over j bins. In the balanced allocation
    # the sizes are q and q+1. At a=y*10^power, (n-d+1)^h/m is at least
    # L^h/U * y^(h/d-1/j). A nonnegative exponent permits the constant L^h/U.
    for h, count in ((q,j-r),(q+1,r)):
        if h*j>=d and L**h>U:
            top*=L**(h*count)
            bottom*=U**count
    return top,bottom


def possible_pair(j,d,cap,power,large,no_empty):
    if (j,d) in PUBLISHED:
        return False
    fact = factorial(d)
    L = scales(d,power)-d+1
    for empty in range(max(0,d-cap),d+1):
        if empty and no_empty:
            break
        empty_cost=L**empty
        if empty_cost>fact:
            break
        S=max(0,2*(d-empty)-cap)
        top,bottom=grouped_bound(j,d,S,power)
        if empty_cost*top>fact*bottom:
            continue
        if empty_cost*weight_minimum(j,d,S,power,large)>fact:
            continue
        return True
    return False


def check(cap,power,large=False,no_empty=False):
    assert cap in (12,13,14) and power>=100
    N=root(10**power,cap)
    # Every row n satisfies n>=N via a<=n^cap. For n>=t>cap the function
    # C(n,t)/n^cap increases, directly from its falling-factorial product.
    t=next(i for i in range(cap+1,17) if 2*i<=N and comb(N,i)>N**cap)
    edges = {p for p in combinations(range(2,t),2) if not possible_pair(*p,cap,power,large,no_empty)}
    remaining = [c for c in combinations(range(2,t),4)
                 if all(p not in edges for p in combinations(c,2))]
    return t,edges,remaining


def verify_fifteen():
    """Close the four exceptional pairs in the 10^100 to 10^123 bridge."""
    from bisect import bisect_left, bisect_right
    lower,upper=10**100,10**123
    _,edges,patterns=check(14,100)
    _,large_edges,_=check(14,100,True)
    obligations={(7,11),(10,11),(12,13),(14,15)}
    assert not check(14,123)[2]
    assert obligations <= large_edges-edges
    assert all(obligations.intersection(combinations(c,2)) for c in patterns)
    for j,d in sorted(obligations):
        low,high=scales(d,100),scales(d,123)+d
        divisors=divisors_of_factorial(d)
        # For each prime q>d, C(n,k) mod q depends only on n mod q for k<=d.
        # Every filter below is necessary. The final inversion is exact.
        filters=[]
        for q in (17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97):
            residues={comb(m,j)%q for m in range(q)}
            allowed={n for n in range(q) if comb(n,d)%q in residues}
            filters.append((q,allowed))
        filters.sort(key=lambda z:len(z[1])/z[0])
        rows=set()
        for p in (2,3,5,7,11,13):
            if p>d:
                continue
            Q=p
            while Q<=high:
                start=bisect_left(divisors,max(1,(low-d+1+Q-1)//Q))
                stop=bisect_right(divisors,high//Q)
                for b in divisors[start:stop]:
                    for n in range(max(low,b*Q),min(high+1,b*Q+d)):
                        rows.add(n)
                Q*=p
        exact=0
        for n in rows:
            if any(n%q not in allowed for q,allowed in filters):
                continue
            a=comb(n,d)
            if not lower<=a<=upper:
                continue
            exact+=1
            R=root(factorial(j)*a,j)
            assert all(comb(m,j)!=a for m in range(R,R+j+1)), (j,d,n,a)
        print(f"({j},{d}): {len(rows)} unique candidate rows, "
              f"{exact} exact inversions, zero collisions",flush=True)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--cap',type=int,default=13)
    parser.add_argument('--power',type=int,default=100)
    parser.add_argument('--large-singletons',action='store_true')
    parser.add_argument('--no-empty',action='store_true')
    parser.add_argument('--verify-fifteen',action='store_true',
                        help='also verify the cap-14 graph and finite exceptional pairs')
    a=parser.parse_args()
    t,edges,patterns=check(a.cap,a.power,a.large_singletons,a.no_empty)
    print(f"cap={a.cap}, a>=10^{a.power}, large singleton bases={a.large_singletons}, "
          f"empty hosts excluded={a.no_empty}")
    print(f"Columns below {t}; {len(edges)} excluded pairs; {len(patterns)} remaining patterns: {patterns}")
    if a.verify_fifteen:
        verify_fifteen()
