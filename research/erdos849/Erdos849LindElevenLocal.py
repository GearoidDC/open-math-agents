"""Check the eleventh Lind value's low-row range using a local chain of primes."""

from math import gcd, isqrt

import gmpy2 as g

from Erdos849LindElevenDeep import (
    DEEP, K, N, binomial_log_difference, first_uncovered, known_rows, trial_prime,
)
from Erdos849LindTenth import remainders


BOUND = 1 << 45
CROSSOVER = 175_119_328
FIRST_PRIME = 3_478_759_213


def certified_prime_chain():
    assert trial_prime(FIRST_PRIME) and FIRST_PRIME > N
    stride = CROSSOVER - 1_000
    primorial = g.primorial(isqrt(BOUND + 1_000))
    previous = FIRST_PRIME
    target = previous + stride
    count = 1
    longest = 0
    while target <= BOUND:
        batch = []
        while target <= BOUND and len(batch) < 8192:
            candidate = int(g.next_prime(target))
            assert target < candidate <= target + 1_000
            gap = candidate - previous
            assert 0 < gap <= CROSSOVER
            longest = max(longest, gap)
            batch.append(candidate)
            previous = candidate
            target += stride
        residues = remainders(primorial, batch)
        assert len(residues) == len(batch)
        assert all(gcd(p, r) == 1 for p, r in zip(batch, residues))
        count += len(batch)
    assert BOUND - previous < CROSSOVER
    return count, longest, previous


def main():
    lo, hi = binomial_log_difference(BOUND, CROSSOVER-1, N, K)
    assert -11 < lo <= hi < -10
    lo, hi = binomial_log_difference(BOUND, CROSSOVER, N, K)
    assert 1 < lo <= hi < 2
    assert 2*CROSSOVER < BOUND
    j = DEEP-1
    m = first_uncovered(j)
    assert 2*j < m
    lo, hi = binomial_log_difference(m, j, N, K)
    assert -6 < lo <= hi < -5
    hits = known_rows()
    assert FIRST_PRIME == N+13
    count, longest, last = certified_prime_chain()
    print(f"Boundary row {BOUND:,}; first column above A at this row: {CROSSOVER:,}.")
    print(f"Certified {count:,} primes, largest spacing {longest:,}, last prime {last:,}.")
    print(f"Only proper positions in rows up to {BOUND:,}: {hits}.")
    print(f"For j <= {j:,}, every occurrence has row strictly above {m:,}.")


if __name__ == "__main__":
    main()
