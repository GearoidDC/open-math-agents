"""Count admissible rows of the eleventh Lind–Singmaster value (requires gmpy2)."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from math import comb

import gmpy2 as g

from Erdos849LindTenth import excludes, middle_block, prime_divisors, prime_table
from Erdos849LindElevenDeep import DEEP, K, N, first_uncovered, main as deep


FIRST_MIDDLE = 1_200_000


def lucas_residue(n, k, p):
    digits = []
    while k:
        n, a = divmod(n, p)
        k, b = divmod(k, p)
        if b > a:
            return 0
        digits.append((a, b))
    value = 1
    for a, b in digits:
        # C(a,b) = (-1)^b C(p-1-a+b,b) mod p. Use symmetry before
        # selecting the smaller top argument, to reduce the exact GMP work.
        b = min(b, a-b)
        reflected = p-1-a+b
        if reflected < a:
            a = reflected
            if b % 2:
                value = -value
        value = int(value*g.comb(a,b) % p)
    return value


def residues_block(primes):
    return [(p, y) for p in primes if (y := lucas_residue(N, K, p))]


def cover_block(args):
    start, end, tests = args
    largest = cursor = 0
    for j in range(start, end):
        while cursor < len(tests) and tests[cursor][0] <= j:
            cursor += 1
        for i in range(cursor, len(tests)):
            if excludes(j, *tests[i]):
                largest = max(largest, tests[i][0])
                break
        else:
            raise AssertionError(("uncovered column", j))
    return end-start, largest


def shallow(pool):
    from bisect import bisect_right
    primes = prime_table(FIRST_MIDDLE+30_000)
    for p in primes[:45]:
        for n in (11, 42, 250, 1001):
            for k in (0, 1, 2, n//3, n//2):
                assert lucas_residue(n,k,p) == comb(n,k) % p
    tests = []
    for group in pool.map(residues_block, (primes[i:i+128] for i in range(0,len(primes),128))):
        tests.extend(group)
    # Cross-check the residues against the independent neighboring representation.
    for p,y in tests[::211]:
        assert lucas_residue(N-1,K+1,p) == y
    ps = [p for p,_ in tests]
    blocks = []
    for lo in range(2, FIRST_MIDDLE, 4000):
        hi = min(lo+4000,FIRST_MIDDLE)
        i, j = bisect_right(ps,lo), bisect_right(ps,hi)+25
        blocks.append((lo,hi,tests[i:j]))
    counts = list(pool.map(cover_block,blocks))
    assert sum(c for c,_ in counts) == FIRST_MIDDLE-2
    print(f"Shallow columns excluded: {FIRST_MIDDLE-2:,}; largest witness prime: {max(p for _,p in counts):,}.",flush=True)


def check_intervals(pool, first, stop, row_floor):
    ps = prime_divisors(N,K)
    control = middle_block((15,5,2,6,[],1))[2]
    assert all(any(j==k and lo<=n<=hi for j,lo,hi in control)
               for n,k in ((14,6),(15,5),(78,2)))
    # Keep the early, high-precision blocks short to distribute their cost.
    lo = first
    jobs = []
    while lo < stop:
        hi = min(stop, lo+min(lo//32, 150_000))
        jobs.append((N,K,lo,hi-1,ps,row_floor(lo)))
        lo = hi
    crossed = rejected = covered = 0
    for job,(c,r,hits) in zip(jobs,pool.map(middle_block,jobs)):
        assert not hits and c == r, (job[2:4],hits[:5])
        crossed += c
        rejected += r
        covered += job[3]-job[2]+1
        if job[3]//10_000_000 != (job[2]-1)//10_000_000:
            print(f"Middle columns through {job[3]:,}.",flush=True)
    assert covered == stop-first
    print(f"Columns {first:,} through {stop-1:,}: {covered:,} tested; candidate intervals: {crossed:,}; rejected: {rejected:,}.",flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", choices=("shallow","middle","deep","bridge","local","all"), default="all")
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    if args.part in ("shallow","middle","bridge","all"):
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            if args.part in ("shallow","all"):
                shallow(pool)
            if args.part in ("middle","all"):
                check_intervals(pool,FIRST_MIDDLE,DEEP,first_uncovered)
            if args.part in ("bridge","all"):
                from Erdos849LindElevenLocal import BOUND, CROSSOVER
                check_intervals(pool,DEEP,CROSSOVER,lambda _: BOUND+1)
    if args.part in ("deep","all"):
        deep()
    if args.part in ("local","all"):
        from Erdos849LindElevenLocal import main as local
        local()
