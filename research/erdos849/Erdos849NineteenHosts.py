"""Exclude five-row values with at most nineteen primes and largest column >=18."""

from itertools import combinations
from math import comb, factorial, gcd, lcm, prod

from Erdos849EighteenPrimes import row_bounds
from Erdos849FourteenBound import floor_root
from Erdos849TwelfthPower import equal_in_column


X = 10**128


def divisors(n):
    factors = [1]
    p = 2
    while p*p<=n:
        original = list(factors)
        power = 1
        while n%p==0:
            n //= p
            power *= p
            factors.extend(power*v for v in original)
        p += 1
    return factors if n==1 else factors+[v*n for v in factors]


def empty_terms():
    for k in range(5,23):
        partners = {18,19} if k<18 else set(range(7,k))
        if k==18:
            partners.add(19)
        low,_ = row_bounds(k,X)
        rows = {D+s for D in divisors(lcm(*range(1,k+1))) for s in range(k) if D+s>=low}
        for n in rows:
            a = comb(n,k)
            if a>=X:
                assert all(not equal_in_column(a,j) for j in partners),(k,n)


def sign(n,d,j,b,c,r,offsets):
    row = b*prod(n-s for s in offsets)+c*r
    left = factorial(j)*c**j*prod(n-i for i in range(d))
    right = factorial(d)*prod(row-c*i for i in range(j))
    return left-right


def no_root(d,j,b,c,r,offsets,low):
    left = right = low
    while sign(right,d,j,b,c,r,offsets)<0:
        right *= 2
    while left<right:
        m = (left+right)//2
        if sign(m,d,j,b,c,r,offsets)<0:
            left = m+1
        else:
            right = m
    return sign(left,d,j,b,c,r,offsets)!=0


def pair(j,d):
    lj,uj = row_bounds(j,X)
    ld,ud = row_bounds(d,X)
    q = 1
    while q*j<=d and lj>lcm(*range(1,j+1))*ud**q:
        q += 1
    if q*j>19:
        return 0
    clean = (q+1)*j-19 - 2*(19-d)
    assert clean>0 and q*j<=d
    bmax = floor_root(factorial(j),clean)
    cmax = bmax*ud**q//lj
    searches = 0
    for b in divisors(factorial(j)):
        if b>bmax:
            continue
        for c in range(1,cmax+1):
            if factorial(d)%c or gcd(b,c)!=1 or b*ud**q<c*lj:
                continue
            if q*j==d:
                assert b*ld**q>c*uj
                continue
            assert j*q*ld**q<d*((ld-d+1)**q-j*c)
            for r in range(j):
                for offsets in combinations(range(d),q):
                    assert no_root(d,j,b,c,r,offsets,ld),(d,j,b,c,r,offsets)
                    searches += 1
    return searches


def main():
    assert row_bounds(23,X)[1]**19<X
    assert sign(18,18,8,1,1,6,(16,17))==0
    empty_terms()
    for d in (18,19):
        tests = list(range(7,d))
        if d==18:
            # If column 11 occurs, there is a third proper column outside
            # the classified clique. It is 5 or one of the other tested columns.
            tests.remove(11)
            tests.append(5)
        counts = [(j,pair(j,d)) for j in tests]
        print(f"Largest column {d}: {counts}",flush=True)
    print("At most 19 prime bases: every five-row value has largest column at most 17.")


if __name__=="__main__":
    main()
