"""Replay the finite congruence exclusions for the four-column prime bound."""

from itertools import combinations
from math import comb, factorial, prod
from bisect import bisect_left, bisect_right
from functools import lru_cache

from Erdos849PatternThree import PRIMES, floor_root


def candidate_rows(lo,hi,moduli):
    residues = [0]
    modulus = 1
    index = 0
    while index<len(moduli) and modulus<=hi-lo:
        q = moduli[index]
        inverse = pow(modulus,-1,q)
        residues = [r+modulus*((s-r)*inverse%q) for r in residues for s in range(8)]
        modulus *= q
        index += 1
    return {x for r in residues
            for x in range(lo+(r-lo)%modulus,hi+1,modulus)
            if all(x%q<8 for q in moduli[index:])}


@lru_cache(512)
def wheel(moduli):
    if not moduli:
        return 1,[0]
    m,xs = wheel(moduli[:-1])
    q = moduli[-1]
    inv = pow(m,-1,q)
    return m*q,[x+m*((s-x)*inv%q) for x in xs for s in range(8)]


def joined_rows(lo,hi,moduli):
    split = len(moduli)//2
    m,left = wheel(moduli[:split])
    n,right = wheel(moduli[split:])
    inverse = pow(m,-1,n)
    transformed = sorted(x*inverse%n for x in right)
    result = set()
    for x in left:
        lower,upper = (lo-x+m-1)//m,(hi-x)//m
        if lower>upper:
            continue
        first = (lower+x*inverse)%n
        length = upper-lower
        if length>=n-1:
            allowed = transformed
        else:
            last = first+length
            lower_index = bisect_left(transformed,first)
            if last<n:
                allowed = transformed[lower_index:bisect_right(transformed,last)]
            else:
                allowed = transformed[lower_index:]+transformed[:bisect_right(transformed,last-n)]
        for y in allowed:
            start = lower+(y-first)%n
            result.update(x+m*k for k in range(start,upper+1,n))
    return result


def row_in_column(a,k):
    n = floor_root(factorial(k)*a,k)
    return any(comb(m,k)==a for m in range(n,n+k+1))


def sieve(large=7,join=False,decade=128,budget=34800,rate=36,columns=(3,5,7)):
    cap = 25+large
    end = decade
    assert rate>cap
    while (420*budget**cap)**rate >= 10**(decade*cap+end*(rate-cap)):
        end += 1
    period = 10*rate
    places = (10*(end-decade)+period-1)//period
    base = budget**period*10**(places*period)
    # floor(floor(x)/10^j)=floor(x/10^j). Each fractional decade
    # exponent therefore needs just one integer root across the scan.
    fractional = [floor_root(base*10**v,period) for v in range(period)]
    exceptional = []
    for i in range(10*decade,10*end):
        whole,rem = divmod(i+1-10*decade,period)
        q = 1+fractional[rem]//10**(places-whole)
        powers = {}
        for p in PRIMES:
            z = 1
            while z*p<=q:
                z *= p
            powers[p] = z
        bound = 420*q**large*prod(powers.values())
        if bound**10 < 10**i:
            continue
        # Within the selected set, at most 'omit' bases fail to attain
        # their maximum possible exponent.
        groups = [(p,z) for p,z in powers.items() if p>=31]
        omit = 0
        while (31**(omit+1))**10*10**i <= bound**10:
            omit += 1
        take = 6
        selected = tuple(sorted((z for _,z in groups),reverse=True)[:take+omit])
        assert len(selected)==take+omit
        low = floor_root(factorial(8)**10*10**i,80)
        high = floor_root(factorial(8)**10*10**(i+1),80)+8
        exceptional.append((i,low,high,selected,omit))
    rows = set()
    scan = joined_rows if join else candidate_rows
    if join:
        moduli = (31,37,41,43,47,53)
        for lo,hi in [(17,1000),(10**15,10**15+10**9)]:
            assert joined_rows(lo,hi,moduli)==candidate_rows(lo,hi,moduli)
    # Join adjacent exceptional row ranges having the same congruences.
    merged = []
    for i,lo,hi,selected,omit in exceptional:
        if merged and merged[-1][2:]==(selected,omit) and merged[-1][1]>=lo-1:
            merged[-1]=(merged[-1][0],hi,selected,omit)
        else:
            merged.append((lo,hi,selected,omit))
    for lo,hi,selected,omit in merged:
        for required in combinations(selected,len(selected)-omit):
            rows.update(scan(lo,hi,required))
    matches = []
    for n in sorted(rows):
        a = comb(n,8)
        if all(row_in_column(a,k) for k in columns):
            matches.append(n)
    assert not matches, matches
    print(f"At most {large} primes above 100: {len(exceptional)} exceptional "
          f"tenth-decades, {len(merged)} congruence ranges, {len(rows)} candidate rows, "
          f"zero four-column values.",flush=True)
    return len(exceptional),len(merged),len(rows)


if __name__=="__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--large",type=int,default=9)
    parser.add_argument("--join",action="store_true",help="use a pair of CRT wheels")
    args = parser.parse_args()
    assert 5<=args.large<=9
    sieve(args.large,args.join or args.large>=9)
