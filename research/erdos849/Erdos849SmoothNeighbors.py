"""Check large prime divisors using the complete Luca–Najman smooth-neighbor list."""

import gzip
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from math import comb, factorial, isqrt
from pathlib import Path


HEIGHT = 10**128
PRIMES = tuple(p for p in range(2, 101)
               if all(p % k != 0 for k in range(2, isqrt(p) + 1)))


@lru_cache(maxsize=50000)
def is_smooth(value):
    assert value > 0
    for p in PRIMES:
        while value % p == 0:
            value //= p
    return value == 1


def smooth_neighbors():
    with gzip.open(Path(__file__).with_suffix(".txt.gz"), "rt", encoding="ascii") as handle:
        centers = [int(line) for line in handle]
    assert len(set(centers)) == len(centers) == 16223 and min(centers) == 2
    assert all(is_smooth(c - 1) and is_smooth(c + 1) for c in centers)
    # Each tuple contains two positive 100-smooth numbers one or two apart.
    pairs = {(c - 1, c + 1) for c in centers}
    pairs.update(((c - 1) // 2, (c + 1) // 2) for c in centers if c % 2)
    return sorted(pairs)


def first_deep_column(omega):
    k = omega + 1
    while True:
        # The deliberately loose ceiling below is integer-only.
        lower, upper = 0, 2
        while upper**k < factorial(k) * HEIGHT:
            upper *= 2
        while upper - lower > 1:
            middle = (lower + upper) // 2
            if middle**k < factorial(k) * HEIGHT:
                lower = middle
            else:
                upper = middle
        if (upper + k)**omega < HEIGHT:
            return k
        k += 1


def largest_supported(pairs, min_column, max_column, exceptional):
    assert min_column - 1 < 3 * (min_column - exceptional - 1)
    # All candidates contain a pair within distance two. Collect their end rows.
    rows = set()
    for left, right in pairs:
        rows.update(range(right, left + max_column))
    peak = (0, 0, 0)
    for n in rows:
        kmax = min(max_column, n // 2)
        if kmax < min_column:
            continue
        bad = 0
        for k in range(1, kmax + 1):
            bad += not is_smooth(n - k + 1)
            if bad > exceptional:
                break
            if k >= min_column:
                peak = max(peak, (comb(n, k), n, k))
    return peak


def smooth_multiplicities(pairs):
    proper = defaultdict(list)
    for left, n in pairs:
        if n != left + 1:
            continue
        for k in range(2, n // 2 + 1):
            if not is_smooth(n - k + 1):
                break
            proper[comb(n, k)].append((n, k))
    counts = Counter(len(rows) + 1 for rows in proper.values())
    triples = sorted(a for a, rows in proper.items() if len(rows) == 2)
    quadruples = sorted(a for a, rows in proper.items() if len(rows) == 3)
    assert counts == {2: 16748, 3: 6, 4: 1}
    assert triples == [120, 210, 1540, 7140, 11628, 24310] and quadruples == [3003]
    assert proper[3003] == [(14, 6), (15, 5), (78, 2)]
    print(f"100-smooth values with 2, 3, 4 rows: {counts[2]}, {counts[3]}, {counts[4]}.")


def main(extended=False):
    pairs = smooth_neighbors()
    deep = first_deep_column(len(PRIMES) + 4)
    assert deep == 40
    peak = largest_supported(pairs, 8, deep - 1, 4)
    print(f"Checked {len(pairs)} neighboring pairs and columns 8 through {deep-1}.")
    print(f"Maximum with at most four nonsmooth numerator terms: {peak}.")
    assert peak == (comb(11997652, 8), 11997652, 8) and peak[0] < HEIGHT
    smooth_multiplicities(pairs)
    if extended:
        for limit in range(5, 13):
            kmin = (3 * limit + 2) // 2 + 1
            deep = first_deep_column(len(PRIMES) + limit)
            assert deep < 101
            peak = largest_supported(pairs, kmin, deep - 1, limit)
            assert peak[0] < HEIGHT
            print(f"For columns >= {kmin}, at least {limit+1} distinct primes exceed 100.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extended", action="store_true", help="also check larger column cutoffs")
    main(parser.parse_args().extended)
