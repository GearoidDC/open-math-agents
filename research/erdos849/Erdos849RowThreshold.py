"""Check prime-factor restrictions for values shared by the two column-eight patterns.

Run with --case count to exclude at most twelve primes above 100, or with
--case largest to exclude prime support contained in the primes through 167.
Both cases use the archived pointwise bound with Q=35519 and rate 36.
"""

from argparse import ArgumentParser
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations
from math import comb, factorial, isqrt, prod
from time import monotonic

from Erdos849PatternCapTen import filters, row_root
from Erdos849PatternThreshold import BUDGET, RATE, START, stream
from Erdos849PatternThree import floor_root, host_loss, root
from Erdos849PatternThreeCRT import row_in_column


def primes_through(limit):
    return [p for p in range(2, limit+1)
            if all(p % divisor for divisor in range(2, isqrt(p)+1))]


def endpoint(prime_count):
    """Bound the last possible four-power positions in the eighth column."""
    # Once every position has at least four powers, at least 40-prime_count
    # positions have exactly four. Otherwise more than prime_count are used.
    needed = 40-prime_count
    assert needed in (1, 3)
    positions = combinations(range(8), needed)
    loss = max(prod(host_loss(offsets, p) for p in (2, 3, 5, 7))
               for offsets in positions)
    assert loss == {1: 117600, 3: 2822400}[needed]
    lower = root(8, START)-7
    decade = START
    while True:
        ten = 10**(decade-START)
        three_excluded = lower**24 * ten > (117600 * BUDGET**3)**24
        # Each four-power position gives a factor T^(1/8-4/36)=T^(1/72).
        four_excluded = lower**(72*needed) * ten**needed > (
            loss * BUDGET**(4*needed))**72
        if three_excluded and four_excluded:
            return decade
        decade += 1


def make_plan(primes, outside, end):
    period = 10*RATE
    places = (10*(end-START)+period-1)//period
    base = BUDGET**period * 10**(period*places)
    fractional = [floor_root(base*10**v, period) for v in range(period)]
    ranges = []
    for band in range(10*START, 10*end):
        whole, remainder = divmod(band+1-10*START, period)
        cap = 1+fractional[remainder]//10**(places-whole)
        powers = []
        for p in primes:
            power = 1
            while power*p <= cap:
                power *= p
            denominator = 420
            while denominator % p == 0:
                denominator //= p
                power *= p
            powers.append((p, power))
        upper = cap**outside * prod(power for _, power in powers)
        allowed_loss = floor_root(upper**10//10**band, 10)
        if not allowed_loss:
            continue
        description = tuple(powers)
        if ranges and ranges[-1][1] == band and ranges[-1][2] == description:
            first, _, _, previous_loss = ranges[-1]
            ranges[-1] = first, band+1, description, max(previous_loss, allowed_loss)
        else:
            ranges.append((band, band+1, description, allowed_loss))
    return ranges


def geometry_score(targets, width):
    """An integer estimate of join work, used only to select congruences."""
    # Estimate the total number of rows over every six-element subset
    # by width*8^6 times the sixth elementary symmetric sum of 1/modulus.
    numerators = [1]+[0]*6
    for _, modulus, _ in targets:
        for size in range(6, 0, -1):
            numerators[size] = numerators[size]*modulus+numerators[size-1]
        numerators[0] *= modulus
    denominator = numerators[0]
    expected_rows = width * 8**6 * numerators[6]
    joins = comb(len(targets), 6)
    return 200*joins*denominator+2*expected_rows, denominator


def select_targets(powers, allowed_loss, width):
    best = None
    best_score = None
    floors = [8]+[max(8, floor_root(width**exponent, 30))
                  for exponent in (3, 4, 5, 6)]
    scored = {}
    for depth in range(9):
        for minimum in floors:
            targets = []
            for p, maximum in powers:
                modulus, loss = maximum, p
                for _ in range(depth):
                    if modulus//p < minimum:
                        break
                    modulus //= p
                    loss *= p
                if modulus > 7:
                    targets.append((p, modulus, loss))
            for weight in (1, 3, 7):
                ranked = sorted(targets, key=lambda t: t[1]*t[2]**weight, reverse=True)
                for size in range(6, len(ranked)+1):
                    chosen = tuple(ranked[:size])
                    losses = sorted(cost for _, _, cost in chosen)
                    if prod(losses[:size-5]) <= allowed_loss:
                        continue
                    if chosen not in scored:
                        scored[chosen] = geometry_score(chosen, width)
                    numerator, denominator = scored[chosen]
                    if best is None or numerator*best_score[1] < best_score[0]*denominator:
                        best, best_score = chosen, (numerator, denominator)
                    break
    assert best is not None, "No six-power cover found."
    return best


def terminal_moduli(targets, allowed_loss, width):
    def visit(index, loss, moduli, modulus):
        count = len(moduli)
        if count == 6 or (count >= 4 and 48*modulus >= width*8**count):
            yield moduli
            return
        assert index < len(targets)
        _, target, missed_cost = targets[index]
        yield from visit(index+1, loss, moduli+(target,), modulus*target)
        if loss*missed_cost <= allowed_loss:
            yield from visit(index+1, loss*missed_cost, moduli, modulus)
    yield from visit(0, 1, (), 1)


def run_range(group):
    first, stop, powers, allowed_loss = group
    lower, upper = row_root(first), row_root(stop)+8
    width = upper-lower+1
    targets = select_targets(powers, allowed_loss, width)
    maxima = dict(powers)
    assert len({p for p, _, _ in targets}) == len(targets)
    for p, modulus, missed_cost in targets:
        assert modulus > 7 and maxima[p] % modulus == 0
        assert modulus * missed_cost == p * maxima[p]
    losses = sorted(cost for _, _, cost in targets)
    assert prod(losses[:len(targets)-5]) > allowed_loss

    totals = [0]*5
    cache = {}
    modular_checks = filters()
    # In the smooth case the entire numerator 8!*a must divide this
    # integer. Checking its constituent factors usually stops at n.
    smooth_numerator = factorial(8)*prod(maxima.values()) if 167 in maxima else 0
    for moduli in terminal_moduli(targets, allowed_loss, width):
        totals[len(moduli)-4] += 1
        for row in stream(lower, upper, moduli, cache):
            totals[3] += 1
            if smooth_numerator:
                if smooth_numerator % row == 0:
                    totals[4] += 1
                    assert any(smooth_numerator % (row-offset)
                               for offset in range(1, 8)), row
            elif all(accepted[row % p] for p, accepted in modular_checks):
                totals[4] += 1
                value = comb(row, 8)
                assert not (row_in_column(value, 5) and row_in_column(value, 7)), row
    return totals


def main(case, workers):
    if not __debug__:
        raise RuntimeError("This verifier requires Python assertions.")
    limit, outside = {"count": (100, 12), "largest": (167, 0)}[case]
    primes = primes_through(limit)
    end = endpoint(len(primes)+outside)
    expected_end = {"count": 400, "largest": 611}[case]
    assert end == expected_end
    started = monotonic()
    ranges = make_plan(primes, outside, end)
    print(f"Case {case} has {len(ranges)} finite row ranges and a tail "
          f"from 10^{end}.", flush=True)
    ranges.sort(key=lambda g: g[3], reverse=True)
    totals = [0]*5
    with ProcessPoolExecutor(workers) as pool:
        jobs = [pool.submit(run_range, group) for group in ranges]
        for completed, job in enumerate(as_completed(jobs), 1):
            totals = [a+b for a, b in zip(totals, job.result())]
            if completed % 50 == 0:
                print(f"Checked {completed} of {len(ranges)} ranges.", flush=True)
    print(f"Four-, five-, and six-modulus choices {totals[:3]}. "
          f"Of {totals[3]:,} row visits, {totals[4]:,} reached the final "
          f"{'numerator divisibility' if case == 'largest' else 'binomial membership'} checks. "
          f"Zero surviving rows. Elapsed {monotonic()-started:.1f} seconds.", flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=("count", "largest"), required=True)
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    main(args.case, args.workers)
