"""Sieve a term with five assigned primes in an eighth-column row."""

from itertools import combinations
from math import comb, factorial, lcm

from Erdos849LocalInterpolation import floor_root
from Erdos849RowThreshold import primes_through


def admissible_offsets(term, prime):
    return sum(1<<s for s in range(8) if (term+s)%prime < 8)


def suffix_filters(suffixes, tests):
    filters = []
    for p in tests:
        residues = [v%p for _,v in suffixes]
        possible = [bool(admissible_offsets(r,p)) for r in range(p)]
        masks = []
        for x in range(p):
            packed = bytearray((len(residues)+7)//8)
            for i,v in enumerate(residues):
                if possible[x*v%p]:
                    packed[i//8] |= 1<<(i%8)
            masks.append(int.from_bytes(packed,'little'))
        filters.append((p,masks))
    return filters


def search(largest, height):
    primes = primes_through(largest)
    missing = len(primes)-40
    assert 0 <= missing <= 3
    pool = primes[7-missing:]
    assert min(pool)>7
    cap = 1+floor_root(35519**36*10**(height-128),36)
    assert cap**36 > 35519**36*10**(height-128)
    powers = []
    for p in pool:
        options = []
        v = p
        while v<=cap:
            options.append(v)
            v *= p
        powers.append(options)
    cofactor_bound = lcm(420,*(8*comb(7,r) for r in range(8))) if missing else 420
    cofactors = [i for i in range(1,cofactor_bound+1) if cofactor_bound%i==0]
    suffixes = [(i,v*d) for i,options in enumerate(powers)
                for v in options for d in cofactors]
    # Each prime divisor p>7 of the value requires n_8 mod p in 0,...,7.
    # A prospective term x can then occur only if (x+s) mod p < 8 for some s.
    tests = primes[-(min(len(primes)-4,9*(missing+1))):][::-1]
    filters = suffix_filters(suffixes,tests)
    blocks = [filters[j::missing+1] for j in range(missing+1)]
    higher = [sum(1<<t for t,(i,_) in enumerate(suffixes) if i>j)
              for j in range(len(pool))]
    checks = visits = 0
    survivors = set()
    lower = floor_root(40320*10**137,8)-7
    upper = floor_root(40320*10**height,8)+8
    for a,b,c,d in combinations(range(len(pool)-1),4):
        initial = higher[d]
        for x in powers[a]:
            for y in powers[b]:
                xy = x*y
                for z in powers[c]:
                    xyz = xy*z
                    for t in powers[d]:
                        prefix = xyz*t
                        visits += 1
                        # At most 'missing' tests can fail. At least one of
                        # the disjoint blocks therefore consists of successes.
                        keep = 0
                        for block in blocks:
                            possible = initial
                            for p,table in block:
                                possible &= table[prefix%p]
                                if not possible:
                                    break
                            keep |= possible
                        while keep:
                            bit = keep & -keep
                            keep ^= bit
                            checks += 1
                            term = prefix*suffixes[bit.bit_length()-1][1]
                            if not lower <= term <= upper:
                                continue
                            for s in range(8):
                                n = term+s
                                if sum(n%p>=8 for p in primes if p>7) <= missing:
                                    survivors.add(n)
    for n in survivors:
        value = comb(n,8)
        for k in (5,7):
            low = floor_root(value*factorial(k),k)
            if all(comb(row,k)!=value for row in range(low,low+k+1)):
                break
        else:
            raise AssertionError(('common row',n))
    print(largest,height,visits,checks,len(survivors),flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    search(191,250)
