"""Count the rows of the tenth Lind–Singmaster value. Requires gmpy2."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from math import comb, gcd, isqrt

import gmpy2 as g


N, K = 507_544_127, 193_864_605
FIRST_MIDDLE = 300_000
DEEP = (N+37)//38
LOCAL_DEEP = (N+14)//15
# A certified prime beyond all deep-column rows and inside the published table.
ENDPOINT = 3_999_786_906_849_116_161


def prime_table(limit):
    sieve = bytearray([1])*(limit+1)
    sieve[:2] = bytes(2)
    for p in range(2,isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit-p*p)//p+1)
    return [p for p,v in enumerate(sieve) if v]


def remainders(value, primes):
    levels = [list(map(g.mpz,primes))]
    while len(levels[-1])>1:
        level = levels[-1]
        levels.append([level[i]*level[i+1] if i+1<len(level) else level[i]
                       for i in range(0,len(level),2)])
    rs = [value % levels[-1][0]]
    for level in reversed(levels[:-1]):
        rs = [rs[i//2]%p for i,p in enumerate(level)]
    return list(map(int,rs))


def excludes(j,p,y):
    d = p-1-j
    v = 1
    for s in range(d//2+1):
        if (v if (d-s)%2==0 else p-v)==y or (v if s%2==0 else p-v)==y:
            return False
        if s<d//2:
            v = v*(d-s)*pow(s+1,-1,p)%p
    return True


def low_columns(a):
    primes = prime_table(FIRST_MIDDLE+20000)
    residues = remainders(a,primes)
    # The other known row gives an independent Lucas check on the remainder tree.
    for i in range(0,len(primes),467):
        p = primes[i]
        n,k = N-1,K+1
        y = 1
        while k and y:
            n,ndigit = divmod(n,p)
            k,kdigit = divmod(k,p)
            y = 0 if kdigit>ndigit else int(y*g.comb(ndigit,kdigit)%p)
        assert y==residues[i]
    tests = [(p,y) for p,y in zip(primes,residues) if y]
    for p in (11,17):
        for j in range(2,p):
            image = {comb(n,j)%p for n in range(p)}
            assert all(excludes(j,p,y)==(y not in image) for y in range(1,p))
    cursor = largest = 0
    for j in range(2,FIRST_MIDDLE):
        while tests[cursor][0]<=j:
            cursor += 1
        i = cursor
        while i<len(tests) and not excludes(j,*tests[i]):
            i += 1
        assert i<len(tests), j
        largest = max(largest,tests[i][0])
    return largest


def log_target(n,k,down,up):
    lower = down.lngamma(n+1)
    upper = up.lngamma(n+1)
    for z in (k+1,n-k+1):
        lower = down.sub(lower,up.lngamma(z))
        upper = up.sub(upper,down.lngamma(z))
    return lower,upper


def prime_divisors(n,k):
    # Each certified prime is larger than k and occurs in the numerator.
    # Trial division here keeps probable-prime selection out of the proof.
    lower = max(k,n-k)
    result = []
    for i in range(32):
        p = int(g.next_prime(lower + (n-lower)*(i+1)//33))
        assert lower<p<=n and all(p%d for d in range(2,isqrt(p)+1))
        result.append(p)
    return result


def middle_block(args):
    n,k,first,last,primes,remote = args
    bits = (n+first-1)//first + 96
    down = g.context(precision=bits,round=g.RoundDown)
    up = g.context(precision=bits,round=g.RoundUp)
    lo,hi = log_target(n,k,down,up)
    lo = down.add(lo,down.lngamma(first))
    hi = up.add(hi,up.lngamma(first))
    crossed = rejected = 0
    hits = []
    for j in range(first,last+1):
        logj = down.log(j)
        lo = down.add(lo,logj)
        hi = up.add(hi,up.next_above(logj))
        left = down.exp(down.div(lo,j))
        right = up.exp(up.div(hi,j))
        assert left>0
        # All represented rows m obey R+u <= m <= R+u+u²/(2R),
        # where R=(j! A)^(1/j) and u=(j-1)/2.
        half = down.div(j-1,2)
        low = down.add(left,half)
        high = up.add(up.add(right,half),up.div((j-1)**2,down.mul(8,left)))
        # Compare the upper end first, because most intervals miss every integer.
        m = int(down.floor(high))
        if m<low or m<remote:
            continue
        start = max(remote,int(up.ceil(low)))
        crossed += 1
        # Every required prime must divide a numerator in [start-j+1,m].
        if any(m//p == (start-j)//p for p in primes):
            rejected += 1
            continue
        hits.append((j,start,m))
    return crossed,rejected,hits


def known_window():
    nearest = []
    for side in (-1,1):
        p = N if side<0 else N+1
        while not all(p%i for i in range(2,isqrt(p)+1)):
            p += side
        nearest.append(p)
    bottom,first = nearest
    assert N-K<bottom<=N<first
    hits = []
    for m in range(bottom,first):
        j = K
        num = den = 1
        for r in range(N,m):
            num *= r+1
            den *= r+1-K
        for r in range(N,m,-1):
            num *= r-K
            den *= r
        while num>den and j>1:
            num *= j
            den *= m-j+1
            j -= 1
        while num<den and 2*(j+1)<=m:
            num *= m-j
            den *= j+1
            j += 1
        if num==den:
            hits.append((m,j))
    return bottom,first,hits


def run_middle(workers,external):
    ps = prime_divisors(N,K)
    # Check the integer interval routine on known non-edge occurrences.
    control = middle_block((15,5,2,6,[],1))[2]
    assert all(any(j==k and lo<=n<=hi for j,lo,hi in control)
               for n,k in ((14,6),(15,5),(78,2)))
    jobs = []
    deep = DEEP if external else LOCAL_DEEP
    remote = ENDPOINT if external else LOCAL_DEEP*2**15+1
    first = FIRST_MIDDLE
    while first<deep:
        last = min(deep-1, first+min(first//3,150000)-1)
        jobs.append((N,K,first,last,ps,remote))
        first = last+1
    crossed = rejected = 0
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for job,(c,r,hits) in zip(jobs,pool.map(middle_block,jobs)):
            assert not hits, (job[2:4],hits[:8])
            crossed += c
            rejected += r
            if (job[3]//2000000)!=(job[2]//2000000):
                print(f"Checked through column {job[3]:,}.",flush=True)
    print(f"Middle columns: {deep-FIRST_MIDDLE:,}. Candidate intervals: {crossed}; excluded: {rejected}.")


def local_prime_cover(first):
    bound = LOCAL_DEEP*2**15
    # A>=2^K and A<=m^j imply j >= ceil(K / bit_length(bound)).
    span = (K+bound.bit_length()-1)//bound.bit_length()
    stride = span-1000
    assert stride>1000
    # The candidate finder may use probable primality. A product/remainder
    # tree tests each candidate against every prime <=sqrt(bound+1000).
    primorial = g.primorial(isqrt(bound+1000))
    previous = first
    i = first+stride
    count = 1
    max_gap = 0
    while i<=bound:
        candidates = []
        while i<=bound and len(candidates)<8192:
            q = int(g.next_prime(i))
            assert i<q<=i+1000 and q-previous<=span
            candidates.append(q)
            max_gap = max(max_gap,q-previous)
            previous = q
            i += stride
        assert all(gcd(q,r)==1 for q,r in zip(candidates,remainders(primorial,candidates)))
        count += len(candidates)
    assert bound-previous<span
    print(f"Certified {count:,} primes covering rows through {bound:,}; greatest spacing {max_gap:,}.")


def high_columns(external):
    bottom,first,hits = known_window()
    assert hits==[(N-1,K+1),(N,K)]
    if external:
        assert ENDPOINT<4*10**18 and DEEP*2**38 < ENDPOINT
        assert (ENDPOINT-1)%(2**41)==2**40 and ENDPOINT<2**80
        assert pow(17,(ENDPOINT-1)//2,ENDPOINT)==ENDPOINT-1
        assert FIRST_MIDDLE>1476
    else:
        local_prime_cover(first)
    print(f"Prime endpoints {bottom} and {first}. Proper rows in their gap: {hits}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part',choices=['low','middle','high','all'],default='all')
    parser.add_argument('--workers',type=int,default=4)
    parser.add_argument('--published-gaps',action='store_true',
                        help='use the published prime-gap table for a shorter run')
    args = parser.parse_args()
    fib = [0,1]
    while len(fib)<=23:
        fib.append(fib[-1]+fib[-2])
    assert (N,K)==(fib[22]*fib[23],fib[20]*fib[23])
    if args.part in ('low','all'):
        a = g.comb(N,K)
        digits = a.num_digits(10)
        if a < g.mpz(10)**(digits-1):
            digits -= 1
        assert g.mpz(10)**(digits-1)<=a<g.mpz(10)**digits
        print(f"Digits: {digits:,}; low columns: {FIRST_MIDDLE-2:,}; largest prime witness: {low_columns(a)}.")
    if args.part in ('middle','all'):
        run_middle(args.workers,args.published_gaps)
    if args.part in ('high','all'):
        high_columns(args.published_gaps)


if __name__=='__main__':
    main()
