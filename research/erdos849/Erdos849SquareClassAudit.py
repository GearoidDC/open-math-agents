"""Replay the columns 7/8 finite exclusion directly on the row-number recurrence."""

from functools import cache
from itertools import combinations, product
from math import comb, gcd, isqrt


@cache
def unit(d):
    for v in range(1, 1001):
        u = isqrt(1+d*v*v)
        if u*u == 1+d*v*v:
            return u,v
    raise ArithmeticError(d)


def row_seeds():
    classes = [d for d in range(1,211) if 210 % d == 0]
    for i,j in combinations(range(8),2):
        for d,e in product(classes, repeat=2):
            if d == e:
                continue
            g = gcd(d,e)
            D = d*e//g**2
            U,V = unit(D)
            for b in range(isqrt(V*V*d*(j-i)-1)//g+1):
                n = e*b*b+j
                a = isqrt((n-i)//d)
                if d*a*a != n-i:
                    continue
                # After multiplication by U+V sqrt(D), (x/d)'=Ua+V(e/g)b.
                first = d*(U*a+V*(e//g)*b)**2+i
                yield n, first, 4*U*U-2, i+j


def images():
    for p in range(11,1100):
        if any(p % q == 0 for q in range(2,isqrt(p)+1)):
            continue
        seven = {comb(r,7)%p for r in range(p)}
        yield p, tuple(comb(r,8)%p in seven for r in range(p))


def residues(n0, n1, scale, offset_sum, p, allowed_rows):
    a,b = start = (n0%p,n1%p)
    constant = ((2-scale)//2*offset_sum)%p
    good = []
    while True:
        good.append(allowed_rows[a])
        a,b = b,(scale*b-a+constant)%p
        if (a,b) == start:
            return good
        assert len(good) <= 2*p


def in_seventh_column(value):
    lo,hi = 13,14
    while comb(hi,7) < value:
        hi *= 2
    while lo+1 < hi:
        mid = (lo+hi)//2
        if comb(mid,7) < value:
            lo = mid
        else:
            hi = mid
    return comb(hi,7) == value


def main():
    end = 210000
    primes = tuple(images())
    cases = 0
    for n0,n1,scale,offset_sum in row_seeds():
        cases += 1
        flags = bytearray(b"\x01")*end
        for p, permitted in primes:
            local = residues(n0,n1,scale,offset_sum,p,permitted)
            length = len(local)
            for k,good in enumerate(local):
                if not good:
                    flags[k::length] = bytes((end-1-k)//length+1)
            if flags.find(1,2) < 0:
                break
        assert flags.find(1,2) < 0
        for index, n in enumerate((n0,n1)):
            if flags[index] and n >= 16:
                assert not in_seventh_column(comb(n,8))
    assert cases == 928
    print("Replayed all 928 row orbits through index 209999; no admissible shared value.")


if __name__ == "__main__":
    main()
