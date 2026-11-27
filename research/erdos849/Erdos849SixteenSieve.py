"""Exact simultaneous four-column sieving for the remaining fifteen-prime cases.

Run with no arguments to list row counts. Use --run FIRST LAST to search a
range of pattern indices (inclusive), or --all to search every listed pattern.
Each ordinary four-column collision is tested independently of its prime count.
"""

from argparse import ArgumentParser
from functools import cache
from itertools import combinations
from math import comb
from time import perf_counter

from Erdos849FifteenPrimes import classify
from Erdos849SixteenPrimes import plan
from Erdos849SingletonCertificate import floor_root
from Erdos849Wheel import check_wheel, max_row, search


@cache
def edge(j, d, power):
    return classify(j, d, 10**power, 15)


def obligations():
    lower = 10**100
    row_floor = floor_root(lower, 15)
    cutoff = next(k for k in range(16, 20) if row_floor >= 2*k
                  and comb(row_floor, k) > row_floor**15)
    for pattern in combinations(range(2, cutoff), 4):
        pairs = list(combinations(pattern, 2))
        if any(edge(j, d, 100) is not None for j, d in pairs):
            continue
        for power in range(101, 501):
            if any(edge(j, d, power) is not None for j, d in pairs):
                break
        else:
            raise ValueError(f"No finite cutoff for {pattern}")
        yield pattern, power


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=int, nargs=2, metavar=('FIRST','LAST'))
    parser.add_argument('--all', action='store_true')
    args = parser.parse_args()
    if args.all or args.run:
        check_wheel()
        # The known value 3003 appears at the included upper endpoint and
        # disappears at the excluded lower endpoint.
        assert search(2999,3003,6,(1,2,5))[1] == [(14,(3003,78,15),3003)]
        assert not search(3003,3020,6,(1,2,5))[1]
    pattern_count = row_count = exact_count = 0
    intervals = list(obligations())
    assert dict(intervals) == plan()[1]
    for index, (pattern, power) in enumerate(intervals, 1):
        d = pattern[-1]
        first, last = max_row(10**100,d)+1, max_row(10**power,d)
        print(f"{index:2d} {str(pattern):17} K={power} rows={last-first+1:,} "
              f"[{first:,}, {last:,}]", flush=True)
        if args.all or args.run and args.run[0] <= index <= args.run[1]:
            start = perf_counter()
            count, matches = search(10**100,10**power,d,pattern[:-1])
            print(f"   completed: exact checks={count} matches={matches} "
                  f"seconds={perf_counter()-start:.2f}", flush=True)
            assert not matches
            pattern_count += 1
            row_count += last-first+1
            exact_count += count
    if args.all or args.run:
        print(f"Covered {pattern_count} patterns and {row_count:,} row-pattern pairs; "
              f"{exact_count} exact candidates.")


if __name__ == '__main__':
    main()
