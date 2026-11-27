"""Independently replay the twelve-prime calculation for the two column patterns.

Run with python -B Erdos849PatternThresholdAudit.py --workers 6.
The primary verifier supplies the interval plan. This audit checks every
band, enumerates terminal choices directly, reverses the CRT moduli, and
checks the remaining binomial values by binary search.
"""

from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from functools import lru_cache
from itertools import combinations
from math import comb, factorial, prod
from time import monotonic

from Erdos849PatternThreshold import BUDGET, PRIMES, host_loss, plan
from Erdos849PatternThree import floor_root
from Erdos849PatternThreeCRT import joined_rows


def valuation(number, prime):
    """Return the exponent of prime in a positive integer."""
    assert number > 0
    exponent = 0
    while number % prime == 0:
        number //= prime
        exponent += 1
    return exponent


def audit_host_bounds():
    positions = [
        offsets for size in (1, 4) for offsets in combinations(range(8), size)
    ]
    loss_products = dict.fromkeys(positions, 1)
    for prime in (2, 3, 5, 7):
        period = prime
        while period <= 8:
            period *= prime
        # Lift the primary enumeration by two more base-prime digits.
        period *= prime**2
        maxima = dict.fromkeys(positions, 0)
        for row in range(period + 8, 2 * period + 8):
            valuations = [valuation(row - offset, prime) for offset in range(8)]
            host = valuations.index(max(valuations))
            exponent = valuation(comb(row, 8), prime)
            if exponent:
                assert row % prime**exponent < 8
                valuations[host] += valuation(420, prime) - exponent
            for offsets in positions:
                loss = sum(valuations[offset] for offset in offsets)
                maxima[offsets] = max(maxima[offsets], loss)
        for offsets in positions:
            prime_loss = prime ** maxima[offsets]
            assert prime_loss == host_loss(offsets, prime)
            loss_products[offsets] *= prime_loss

    single_loss = max(loss_products[s] for s in positions if len(s) == 1)
    four_loss = max(loss_products[s] for s in positions if len(s) == 4)
    assert (single_loss, four_loss) == (117600, 8467200)
    lower_factor = floor_root(factorial(8) * 10**128, 8) - 7
    assert lower_factor**24 * 10**(370 - 128) > (single_loss * BUDGET**3)**24
    four_power_bound = (four_loss * BUDGET**16)**18
    assert lower_factor**72 * 10**(369 - 128) <= four_power_bound
    assert lower_factor**72 * 10**(370 - 128) > four_power_bound


def audit_bands(groups):
    """Compute every power cap and loss allowance directly from its band."""
    next_band = 1280
    for first, stop, descriptor, group_loss in groups:
        assert first == next_band and first < stop
        largest_loss = 0
        for band in range(first, stop):
            radicand = BUDGET**360 * 10**(band + 1 - 1280)
            cap = 1 + floor_root(radicand, 360)
            maximal_powers = {}
            for prime in PRIMES:
                permitted_loss = prime ** valuation(420, prime)
                power = permitted_loss
                while power * prime <= cap * permitted_loss:
                    power *= prime
                maximal_powers[prime] = power
            assert maximal_powers == dict(descriptor)
            upper = cap**11 * prod(maximal_powers.values())
            lower_tenth_power = 10**band
            loss = floor_root(upper**10 // lower_tenth_power, 10)
            assert loss**10 * lower_tenth_power <= upper**10
            assert upper**10 < (loss + 1)**10 * lower_tenth_power
            largest_loss = max(largest_loss, loss)
        assert largest_loss == group_loss
        assert prod(sorted(PRIMES)[:20]) > group_loss
        next_band = stop
    assert next_band == 3700 and len(groups) == 140


@lru_cache(None)
def modular_tests():
    """Build the binomial images from falling products in the prime fields."""
    tests = []
    for prime in (101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163):
        images = {}
        for column in (5, 7, 8):
            inverse = pow(factorial(column), -1, prime)
            images[column] = [
                prod(row - i for i in range(column)) * inverse % prime
                for row in range(prime)
            ]
        common = set(images[5]).intersection(images[7])
        tests.append((prime, bytes(value in common for value in images[8])))
    return tests


def column_contains(value, column):
    """Find the first admissible row whose coefficient reaches value."""
    lower = 2 * column - 1
    upper = 2 * column
    while comb(upper, column) < value:
        upper *= 2
    while upper - lower > 1:
        middle = (lower + upper) // 2
        if comb(middle, column) < value:
            lower = middle
        else:
            upper = middle
    return comb(upper, column) == value


@lru_cache(None)
def scaled_row_root(band):
    return floor_root(factorial(8)**10 * 10**band, 80)


def audit_range(group):
    first, stop, descriptor, allowed_loss = group
    primes, powers = zip(*descriptor)
    prefixes = [1]
    for prime in primes:
        prefixes.append(prefixes[-1] * prime)
    row_min = scaled_row_root(first)
    row_max = scaled_row_root(stop) + 8
    width = row_max - row_min + 1
    tests = modular_tests()
    choices = Counter()
    row_visits = 0
    surviving_rows = []
    for size in (4, 5, 6):
        for indices in combinations(range(len(primes)), size):
            # All unselected bases before the last selection are missed.
            selected_product = prod(primes[i] for i in indices)
            if prefixes[indices[-1] + 1] > allowed_loss * selected_product:
                continue
            moduli = [powers[i] for i in indices]
            # Identify the first terminal prefix of this explicit combination.
            stops_at_four = 48 * prod(moduli[:4]) >= width * 8**4
            if stops_at_four != (size == 4):
                continue
            if size >= 5:
                stops_at_five = 48 * prod(moduli[:5]) >= width * 8**5
                if stops_at_five != (size == 5):
                    continue
            choices[size] += 1
            rows = joined_rows(row_min, row_max, tuple(reversed(moduli)))
            row_visits += len(rows)
            for row in rows:
                if all(accepted[row % prime] for prime, accepted in tests):
                    coefficient = comb(row, 8)
                    assert not (column_contains(coefficient, 5)
                                and column_contains(coefficient, 7)), row
                    surviving_rows.append(row)
    return choices, row_visits, surviving_rows


def main(workers):
    if not __debug__:
        raise RuntimeError("This audit requires Python assertions.")
    started = monotonic()
    audit_host_bounds()
    tail_decade, groups = plan()
    assert tail_decade == 370
    audit_bands(groups)
    print("Verified all host bounds and 2,420 tenth-decades.", flush=True)

    choices = Counter()
    row_visits = 0
    surviving_rows = []
    groups.sort(key=lambda group: group[3], reverse=True)
    with ProcessPoolExecutor(workers) as pool:
        jobs = [pool.submit(audit_range, group) for group in groups]
        for completed, job in enumerate(as_completed(jobs), 1):
            group_choices, group_visits, group_rows = job.result()
            choices.update(group_choices)
            row_visits += group_visits
            surviving_rows.extend(group_rows)
            if completed % 35 == 0:
                print(f"Checked {completed} of {len(groups)} ranges.", flush=True)

    assert choices == {4: 93, 5: 655444, 6: 329224}
    assert row_visits == 3541277
    assert len(surviving_rows) == len(set(surviving_rows)) == 45
    print(f"Verified {choices[4]:,} four-modulus, {choices[5]:,} five-modulus and "
          f"{choices[6]:,} six-modulus choices.")
    print(f"Of {row_visits:,} row visits, 45 distinct rows reached exact checks. "
          f"None occurs in both columns. Elapsed {monotonic() - started:.1f} seconds.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    main(args.workers)
