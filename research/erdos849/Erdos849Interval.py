"""Check all C(n,k)=C(m,l) in 10^60 < value <= 10^64, with 7 <= k < l,
k <= n/2, l <= m/2. Uses Python's standard library; no tabulated results as inputs.
"""

from functools import cache
from math import comb, isqrt
from re import finditer
from time import perf_counter


def greatest_row(limit, column):
    """Greatest row n >= column with C(n,column) <= limit (limit >= 1)."""
    lo = column
    # C(n,k) >= (n/k)^k. At hi the right side exceeds limit.
    hi = column << ((limit.bit_length() + column - 1) // column)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if comb(mid, column) <= limit:
            lo = mid
        else:
            hi = mid
    assert comb(lo, column) <= limit < comb(lo + 1, column)
    return lo


def primes_to(limit):
    return [p for p in range(2, limit + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]


@cache
def residues(p, column):
    # For column < p its factorial is invertible mod p, so C(n,column)
    # mod p depends only on n mod p. Include all rows, even indices < column.
    return tuple(comb(r, column) % p for r in range(p))


@cache
def image(p, column):
    return frozenset(residues(p, column))


def surviving_rows(first, last, k, l, primes):
    size = last - first + 1
    # For short ranges an immediate exact check costs less than constructing masks.
    if size <= 100:
        return range(first, last + 1)
    sparse = None
    flags = bytearray(b'\x01') * size
    for p in primes:
        if p <= l:
            continue
        values = image(p, k)
        allowed = bytes(v in values for v in residues(p, l))
        if sparse is None:
            # For each forbidden row residue clear one whole arithmetic progression.
            for residue, ok in enumerate(allowed):
                if not ok:
                    offset = (residue - first) % p
                    if offset < size:
                        flags[offset::p] = bytes(1 + (size - 1 - offset) // p)
            remaining = flags.count(1)
            if remaining <= min(100_000, max(100, size // 64)):
                sparse = [first + match.start() for match in finditer(b'\x01', flags)]
                del flags
        else:
            sparse = [m for m in sparse if allowed[m % p]]
        if sparse is not None and len(sparse) <= 100:
            return sparse
    if sparse is not None:
        return sparse
    return (first + match.start() for match in finditer(b'\x01', flags))


def search(lower, upper, minimum_column, primes):
    """Return all unordered column collisions in the half triangle, excluding lower."""
    matches = []
    pair_count = 0
    initial_count = 0
    checked_count = 0
    l = minimum_column + 1
    # Lower boundary in column l is C(2l,l), strictly increasing with l.
    while comb(2*l, l) <= upper:
        first = max(2*l, greatest_row(lower, l) + 1)
        last = greatest_row(upper, l)
        if first <= last:
            assert lower < comb(first, l) <= comb(last, l) <= upper
            for k in range(minimum_column, l):
                pair_count += 1
                initial_count += last - first + 1
                block_size = 8_000_000
                for block in range(first, last + 1, block_size):
                    block_end = min(block + block_size - 1, last)
                    for m in surviving_rows(block, block_end, k, l, primes):
                        checked_count += 1
                        target = comb(m, l)
                        n = greatest_row(target, k)
                        if n >= 2*k and comb(n, k) == target:
                            matches.append((target, n, k, m, l))
        l += 1
    return sorted(matches), (l - 1, pair_count, initial_count, checked_count)


def self_check(primes):
    # Independent direct enumeration checks the half-triangle convention and both
    # endpoints. This also exercises the sieve on a genuine (2,3) collision.
    lower, upper = 120, 2_000_000
    expected = []
    seen = {}
    k = 2
    while comb(2*k, k) <= upper:
        n = 2*k
        while (value := comb(n, k)) <= upper:
            if lower < value:
                for prev_n, prev_k in seen.get(value, []):
                    expected.append((value, prev_n, prev_k, n, k))
                seen.setdefault(value, []).append((n, k))
            n += 1
        k += 1
    assert search(lower, upper, 2, primes)[0] == sorted(expected)
    assert search(3002, 3003, 5, primes)[0] == [(3003, 15, 5, 14, 6)]
    assert not search(3003, 3004, 5, primes)[0]
    value = comb(104, 39)
    assert search(value - 1, value, 39, primes)[0] == [(value, 104, 39, 103, 40)]


if __name__ == '__main__':
    start = perf_counter()
    primes = primes_to(499)
    self_check(primes)
    matches, (last, pairs, total, exact) = search(10**60, 10**64, 7, primes)
    print(f"10^60 < value <= 10^64; 7 <= k < l <= {last}")
    print(f"{pairs:,} column pairs; {total:,} initial (k,l,m) triples; "
          f"{exact:,} compared exactly after sieving")
    print(f"{len(matches)} collisions: {matches}")
    print(f"Runtime including self-checks: {perf_counter() - start:.2f} s")
