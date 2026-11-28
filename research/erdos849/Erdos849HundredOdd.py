"""Finite odd-exponent prime bound for a collision in columns seven and eight."""

from argparse import ArgumentParser
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
from math import comb, isqrt, prod
from time import monotonic

from Erdos849WiderOdd import kernels, square_pairs
from Erdos849WiderOdd37 import brute_controls, check_kernel, in_seventh_column


MEDIUM = (11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
          59, 61, 67, 71, 73, 79, 83, 89, 97)
LARGE = (101, 103, 107, 109, 113, 127, 131)


def candidate_kernels():
    small = kernels(7)
    result = sorted(prod(group) * divisor
                    for size in range(5) for group in combinations(MEDIUM, size)
                    for divisor in small)
    assert len(set(result)) == len(result) == 16 * sum(comb(21, i) for i in range(5))
    return result


def check_squarefree_bound():
    primes = tuple(p for p in range(11, 132) if all(p % q for q in range(2, isqrt(p) + 1)))
    assert primes == MEDIUM + LARGE
    floor = prod(LARGE)
    assert floor == 228098450046409
    for t in range(7):
        clean = 8 - t
        least_total = min(s + (clean-1)*max(s, 5-s) for s in range(6))
        assert least_total == 23 - 3*t
        if t == 0:
            assert least_total > len(MEDIUM)
        else:
            assert prod(MEDIUM[:least_total]) * prod(LARGE[:t]) >= floor
    assert prod(MEDIUM[:13]) >= floor


def check_batch(args):
    batch, end, cutoff = args
    totals = [0, 0, 0]
    controls, rows = set(), set()
    for d in batch:
        _, steps, orbits, indices, _, direct, candidates, hits = check_kernel(d, end, cutoff)
        assert not hits, (d, hits)
        controls.update((d, *entry) for entry in direct)
        rows.update(candidates)
        totals[0] += steps
        totals[1] += orbits
        totals[2] += indices
    return totals, controls, rows


def main(workers, decade):
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    started = monotonic()
    check_squarefree_bound()
    support = candidate_kernels()
    cutoff = 2000
    direct = brute_controls(cutoff, set(support))
    expected = {(d, *entry) for d, entries in direct.items() for entry in entries if d != 1}
    squares = list(square_pairs(8, 7))
    assert {(n, i, j) for n, i, j in squares if 16 <= n <= cutoff} == direct.get(1, set())
    rows = {n for n, _, _ in squares if n >= 16}
    assert not any(in_seventh_column(n) for n in rows)
    end = 2 + (10 * decade + 3 * 16 + 23) // 24
    assert 24 * (end - 2) >= 10 * decade + 3 * 16
    # Stripe batches across the sorted radicands to balance the continued fractions.
    batches = [support[1 + i::512] for i in range(512)]
    totals = [0, 0, 0]
    verified = set()
    with ProcessPoolExecutor(workers) as pool:
        jobs = ((batch, end, cutoff) for batch in batches)
        for completed, (counts, controls, candidates) in enumerate(pool.map(check_batch, jobs), 1):
            verified.update(controls)
            rows.update(candidates)
            totals = [a + b for a, b in zip(totals, counts)]
            if completed % 32 == 0:
                print(f"{completed}/{len(batches)} batches in {monotonic()-started:.1f}s.", flush=True)
    assert verified == expected
    print(f"10^{decade}, {len(support)-1:,} nonsquare kernels, {totals[0]:,} CF steps, "
          f"{totals[1]:,} orbits, {totals[2]:,} surviving indices, "
          f"{len(verified):,} direct nonsquare controls, {len(rows):,} candidate rows, "
          f"zero common entries. Elapsed {monotonic()-started:.1f}s.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=6)
    parser.add_argument("--decade", type=int, default=3210000)
    args = parser.parse_args()
    if min(args.workers, args.decade) < 1:
        parser.error("workers and decade must be positive")
    main(args.workers, args.decade)
