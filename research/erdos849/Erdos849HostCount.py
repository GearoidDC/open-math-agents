"""Bound the number of prime powers assigned to each column-eight numerator term."""

from functools import cache
from bisect import bisect_left, bisect_right
from itertools import product
from math import comb, factorial, isqrt, prod

from Erdos849PatternThree import floor_root, host_loss, root, valuation
from Erdos849PatternThreeCRT import row_in_column
from Erdos849Wheel import allowed_moduli


Q = 35519
BASE = 128
END = 181
SMALL = (2, 3, 5, 7)


@cache
def local_factors(p, s, q):
    """Possible exact p-parts of n-s, labelled by whether p's power is assigned there."""
    modulus = p
    while modulus <= 8:
        modulus *= p
    cap = p**valuation(420, p) * q
    options = set()
    for residue in range(modulus):
        vals = [valuation((residue-i) % modulus or modulus, p) for i in range(8)]
        host = vals.index(max(vals))
        e = sum(vals) - valuation(factorial(8), p)
        assert 0 <= e <= vals[host]
        if host == s:
            cofactor = p**(vals[s]-e)
            value = p**e
            while value <= cap:
                options.add((cofactor*value, int(value>1)))
                if residue != s:
                    break
                value *= p
        else:
            options.add((p**vals[s], 0))
    return sorted(options)


def intervals(decade, s):
    lower = root(8, decade)-s
    upper = root(8, decade+1)+8-s
    q = floor_root(Q**36*10**(decade+1-BASE),36)+1
    choices = [local_factors(p,s,q) for p in SMALL]
    for factors in product(*choices):
        B = prod(v for v,_ in factors)
        count = sum(c for _,c in factors)
        if not 1 <= count <= 3:
            continue
        lo = (lower+B-1)//B
        hi = min(upper//B, q**(3-count))
        if lo <= hi:
            yield B, 3-count, lo, hi, q


def prime_powers(limit):
    prime = bytearray([1])*(limit+1)
    prime[:2] = bytes(2)
    for p in range(2,isqrt(limit)+1):
        if prime[p]:
            prime[p*p::p] = bytes((limit-p*p)//p+1)
    values = [1]
    for p in range(11,limit+1):
        if prime[p]:
            v = p
            while v<=limit:
                values.append(v)
                v *= p
    return sorted(values)


class Sieve:
    def __init__(self, powers):
        self.powers = powers
        self.allowed = [(p,frozenset(A)) for p,A in allowed_moduli(8,(5,7))]
        self.wheel = [(p,A) for p,A in self.allowed if p<=173][:16]

    @cache
    def masks(self, s):
        tables = []
        for p,A in self.wheel:
            by_residue = [0]*p
            for i,v in enumerate(self.powers):
                by_residue[v%p] |= 1<<i
            table = [0]*p
            for r in range(p):
                for t,mask in enumerate(by_residue):
                    if (r*t+s)%p in A:
                        table[r] |= mask
            tables.append((p,table))
        return tables

    def pairs(self, s, B, low, high, q):
        """Products u*v in [low,high], u<=v<=q, preserving all modular survivors."""
        powers = self.powers
        tables = self.masks(s)
        for u in powers[:bisect_right(powers,min(q,isqrt(high)))]:
            first = bisect_left(powers,max(u,(low+u-1)//u))
            last = bisect_right(powers,min(q,high//u))
            if first>=last:
                continue
            bits = (1<<last)-(1<<first)
            scale = B*u
            for p,T in tables:
                bits &= T[scale%p]
                if not bits:
                    break
            while bits:
                bit = bits & -bits
                yield u*powers[bit.bit_length()-1]
                bits ^= bit

    def rows(self, s, B, unknowns, lo, hi, q):
        if unknowns==2:
            products = self.pairs(s,B,lo,hi,q)
        elif unknowns==1:
            products = self.powers[bisect_left(self.powers,lo):bisect_right(self.powers,hi)]
        else:
            assert unknowns==0 and lo==hi==1
            products = (1,)
        for z in products:
            n = B*z+s
            if all(n%p in A for p,A in self.allowed):
                yield n


def main():
    if not __debug__:
        raise RuntimeError("The certificate uses Python assertions.")
    L = root(8,BASE)-7
    for p in SMALL:
        for n in range(16,2048):
            vals = [valuation(n-i,p) for i in range(8)]
            host = vals.index(max(vals))
            e = valuation(comb(n,8),p)
            for s in range(8):
                assert (p**vals[s], int(host==s and e>0)) in local_factors(p,s,2048)
    for s in range(8):
        no_small = prod(max(v for v,host in local_factors(p,s,1) if not host) for p in SMALL)
        assert 840%no_small==0 and L>no_small*Q**3
    assert max(prod(host_loss((s,),p) for p in SMALL) for s in range(8)) == 117600
    assert (117600*Q**3)**24 < L**24*10**(END-BASE)
    jobs = [(d,s,*item) for d in range(BASE,END) for s in range(8)
            for item in intervals(d,s)]
    sieve = Sieve(prime_powers(max(q for _,_,_,j,_,_,q in jobs if j)))
    # Independently test the two-factor wheel on a short product interval.
    B,s,q = 13,3,3011
    lo,hi = 5*10**6,6*10**6
    powers = [v for v in sieve.powers if v<=q]
    expected = {u*v for u in powers for v in powers if u<=v and lo<=u*v<=hi
                and all((B*u*v+s)%p in A for p,A in sieve.wheel[:2])}
    check = Sieve(sieve.powers)
    check.wheel = check.wheel[:2]
    assert expected and set(check.pairs(s,B,lo,hi,q))==expected
    rows = set()
    for _,s,B,unknowns,lo,hi,q in jobs:
        rows.update(sieve.rows(s,B,unknowns,lo,hi,q))
    matches = [n for n in rows if row_in_column(comb(n,8),5) and row_in_column(comb(n,8),7)]
    assert not matches, matches
    counts = [sum(j==k for _,_,_,j,_,_,_ in jobs) for k in (0,1,2)]
    print(f"Verified {counts} parameter intervals with zero, one, and two additional "
          f"prime powers. {len(rows)} modular survivors, zero matching rows. "
          "Each of the eight numerator terms has at least four assigned primes.")


if __name__=="__main__":
    main()
