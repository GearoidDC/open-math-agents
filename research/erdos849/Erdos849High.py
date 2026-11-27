"""Verify the high-column pair search in 10^64 < value <= 10^100.

If four proper positions exist, at most one can be in {2,3,4,6}, by the
published fixed-pair classifications. Column 5 supplies at most one more.
Thus at least two positions have columns >=7. Here we test all such pairs
whose larger column is >=10, independently of the published finite search.
"""

from math import comb
from time import perf_counter

from Erdos849Interval import primes_to, self_check, surviving_rows
from Erdos849Wheel import allowed_moduli, check_wheel, max_row, survivors


def high_search(lower, upper):
    primes = primes_to(499)
    matches = []
    total_pairs = 0
    total_rows = 0
    total_exact = 0
    l = 10
    start = perf_counter()
    while comb(2*l, l) <= upper:
        first = max(2*l, max_row(lower, l) + 1)
        last = max_row(upper, l)
        if first <= last:
            for k in range(7, l):
                total_pairs += 1
                total_rows += last - first + 1
                if l <= 14:
                    candidates = survivors(first, last, allowed_moduli(l, (k,)))
                else:
                    candidates = (m for block in range(first, last + 1, 8_000_000)
                                  for m in surviving_rows(block, min(last, block + 7_999_999), k, l, primes))
                for m in candidates:
                    total_exact += 1
                    target = comb(m, l)
                    n = max_row(target, k)
                    if n >= 2*k and comb(n, k) == target:
                        matches.append((target, n, k, m, l))
        if l <= 16 or l % 20 == 0:
            print(f"through l={l}  pairs={total_pairs}  "
                  f"exact={total_exact}  elapsed={perf_counter()-start:.2f}s", flush=True)
        l += 1
    assert comb(2*(l-1), l-1) <= upper < comb(2*l, l)
    print(f"Last possible column {l-1}; {total_pairs:,} pairs; "
          f"{total_rows:,} initial triples; {total_exact:,} exact comparisons.")
    print(f"Collisions: {matches}; time {perf_counter()-start:.2f}s")
    return matches


if __name__ == '__main__':
    check_wheel()
    self_check(primes_to(499))
    high_search(10**64, 10**100)
