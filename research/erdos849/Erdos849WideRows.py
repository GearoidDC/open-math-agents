"""Two CRT wheels with arbitrary-size combined period and arbitrary origin."""
import argparse
import ctypes as ct
from itertools import chain, product
from math import ceil, comb, gcd, log, prod
from pathlib import Path
import subprocess
import sys
import os
import shutil
from tempfile import TemporaryDirectory
from time import monotonic
ROOT = Path(__file__).resolve().parent
from Erdos849FocusedCRT import B, I, U, V, Rule, configure, pointers, rules, wheel
from Erdos849Wheel import max_row

def init(cc, directory):
    path = Path(directory) / ('wide.dll' if os.name == 'nt' else 'wide.so')
    source = Path(__file__).with_suffix('.c')
    options = ['-nostdlib', '-fuse-ld=lld'] if os.name == 'nt' else ['-fPIC']
    subprocess.run([cc, '-O3', '-ffreestanding', '-shared', *options, '-o', path, source], check=True)
    dll = ct.CDLL(str(path))
    configure(dll)
    dll.wide_rows.argtypes = [U, U, U, U, V, V, U, V, U, V, V, I, V, V, I, V, V, V, U, V]
    dll.wide_rows.restype = ct.c_int
    dll.wide_phases.argtypes = [V, V, U, U, U, V]
    dll.wide_sort.argtypes = [V, U, U, V, V]
    dll.wide_sort_pairs.argtypes = [V, V, U, U, V, V, V]
    return dll

def get_rules(columns, apply_113, excluded=None):
    out = rules(columns)
    excluded = excluded or {}
    for r in out:
        if r.p in excluded or (apply_113 and r.p == 113):
            values = excluded.get(r.p, set())

            def permitted(n):
                value = comb(n % r.p, 8) % r.p
                return value not in values and (r.p != 113 or not apply_113 or value in (0, 1))
            flags = bytearray((v and permitted(n) for n, v in enumerate(r.flags)))
            r.flags = flags
            r.ids = [n for n, v in enumerate(flags) if v]
    return [r for r in out if 0 < r.density < 1]

def pick(opts, capacity):
    groups = [[], []]
    sizes = [1, 1]
    bases = [1, 1]
    used = set()
    for r in sorted(opts, key=lambda r: log(r.density) / log(max(2, len(r.ids)))):
        if r.p in used:
            continue
        for i in sorted(range(2), key=lambda i: log(sizes[i]) / log(capacity[i])):
            if sizes[i] * len(r.ids) <= capacity[i] and bases[i] * r.period < 1 << 63:
                groups[i].append(r)
                sizes[i] *= len(r.ids)
                bases[i] *= r.period
                used.add(r.p)
                break
    return groups

def optimize_groups(opts, capacity):
    """Find dense modulus products with a feasible split between the two arrays."""
    by_prime = {}
    for rule in opts:
        by_prime.setdefault(rule.p, []).append(rule)
    best = -1
    best_groups = None
    for precision in (50, 120):
        cap = int(precision * log(prod(capacity)))
        dp = [None] * (cap + 1)
        dp[0] = (0, [])
        for choices in by_prime.values():
            updated = dp.copy()
            for rule in choices:
                weight = ceil(precision * log(len(rule.ids)))
                gain = -log(rule.density)
                for i in range(weight, cap + 1):
                    old = dp[i - weight]
                    if old and (updated[i] is None or old[0] + gain > updated[i][0]):
                        updated[i] = (old[0] + gain, old[1] + [rule])
            dp = updated
        for score, selected in sorted((x for x in dp if x), key=lambda x: -x[0]):
            if score <= best:
                break
            selected = sorted(selected, key=lambda r: -len(r.ids))
            splits = []

            def partition(i, groups, sizes, moduli):
                if i == len(selected):
                    if all(groups):
                        splits.append((sizes[1], [s.copy() for s in groups]))
                    return
                rule = selected[i]
                for side in range(2):
                    count = sizes[side] * len(rule.ids)
                    modulus = moduli[side] * rule.period
                    if count <= capacity[side] and modulus < 2 ** 63:
                        new_sizes = sizes.copy()
                        new_sizes[side] = count
                        new_moduli = moduli.copy()
                        new_moduli[side] = modulus
                        groups[side].append(rule)
                        partition(i + 1, groups, new_sizes, new_moduli)
                        groups[side].pop()
            partition(0, [[], []], [1, 1], [1, 1])
            if splits:
                best = score
                best_groups = min(splits, key=lambda a: a[0])[1]
                break
    assert best_groups is not None
    return best_groups

def partitions(opts, groups, mib, block):
    used = {r.p for r in chain(*groups)}
    nr = prod((len(r.ids) for r in groups[1]))
    words = (min(nr, block) + 63) // 64
    masks = []
    budget = mib * 2 ** 20
    for r in sorted(opts, key=lambda r: log(r.density) / r.period ** 0.35):
        cost = 8 * words * r.period
        if r.p not in used and len(masks) < 8 and (cost <= budget):
            masks.append(r)
            used.add(r.p)
            budget -= cost
    tail = []
    for r in sorted(opts, key=lambda r: r.density):
        if r.p not in used:
            tail.append(r)
            used.add(r.p)
    return (masks, tail)

def translated(r, start):
    p = r.period
    a = start % p
    flags = r.flags[a:] + r.flags[:a]
    return Rule(r.p, p, flags, [(x - a) % p for x in r.ids])

def run(dll, lo, hi, groups, masks, tail, verbose=True, block=1500000):
    begin = monotonic()
    assert lo <= hi
    parts = groups + [masks, tail]
    mods = [r.period for r in chain(*parts)]
    assert all((gcd(x, y) == 1 for i, x in enumerate(mods) for y in mods[:i]))
    left_group, right_group, mask_rules, other = ([translated(r, lo) for r in lst] for lst in parts)
    M, left = wheel(dll, left_group)
    N, right = wheel(dll, right_group)
    assert 1 < N < 1 << 63 and 0 < M < 1 << 63
    inv = pow(M, -1, N)
    nl = len(left)
    nr = len(right)
    assert nl * nr < 2 ** 64 and nr and (block > 0)
    # Both products can exceed 64 bits even though each resulting residue fits.
    lookup = (U * (4 * 65536))()
    left_phase = (U * nl)()
    dll.wide_phases(left, left_phase, nl, inv, N, lookup)
    histogram = (U * 65536)()
    temp_key = (U * nl)()
    temp_value = (U * nl)()
    dll.wide_sort_pairs(left_phase, left, nl, N, temp_key, temp_value, histogram)
    del temp_key, temp_value
    dll.wide_phases(right, right, nr, inv, N, lookup)
    ys = right
    sort_scratch = (U * nr)()
    dll.wide_sort(ys, nr, N, sort_scratch, histogram)
    del sort_scratch
    flags = [(B * r.period).from_buffer(r.flags) for r in other]
    mp = (I * len(masks))(*(r.period for r in masks))
    fp = (I * len(tail))(*(r.period for r in tail))
    flag_ptr = pointers(flags)
    size = 8192
    hit_a = (U * size)()
    hit_t = (U * size)()
    totals = [0, 0, 0]
    ans = []
    if verbose:
        description = [(m, n, [rule.period for rule in group])
                       for m, n, group in zip([M, N], [nl, nr], groups)]
        print('wheels', description, 'masks', [r.period for r in masks],
              'setup', round(monotonic() - begin, 2), flush=True)
    scratch = (I * min(nr, block))()
    for offset in range(0, nr, block):
        count = min(nr - offset, block)
        words = (count + 63) // 64
        part = ct.byref(ys, offset * ct.sizeof(U))
        tables = []
        for rule in mask_rules:
            table = (U * (words * rule.period))()
            allowed = (B * (2 * rule.period)).from_buffer_copy(rule.flags + rule.flags)
            dll.make_masks(part, count, M, rule.period, allowed, table, scratch)
            tables.append(table)
        tab_ptr = pointers(tables)
        for origin in range(lo, hi + 1, M * N):
            span = min(hi - origin, M * N - 1)
            maxt, extra = divmod(span, M)
            assert 0 <= maxt < N
            phases = (I * (len(masks) + len(tail)))(*((origin - lo) % r.period for r in chain(masks, tail)))
            counts = (U * 3)()
            result = dll.wide_rows(maxt, extra, M, N, left, left_phase, nl, part, count,
                                   mp, tab_ptr, len(masks), fp, flag_ptr, len(tail),
                                   phases, hit_a, hit_t, size, counts)
            assert result == 0, result
            for i, n in enumerate(counts):
                totals[i] += n
            for i in range(counts[2]):
                a = origin + hit_a[i] + M * hit_t[i]
                assert lo <= a <= hi
                ans.append(a)
    if verbose:
        print('counts', totals, 'elapsed', round(monotonic() - begin, 2), flush=True)
    return (sorted(ans), totals)

def controls(dll):

    def rule(p, ids):
        flags = bytearray(p)
        ids = sorted(set((x % p for x in ids)))
        for i in ids:
            flags[i] = 1
        return Rule(p, p, flags, ids)
    # Modular products and sorting must work immediately below the 63-bit ceiling.
    xs = [(2 ** 63 - 167) * i // 199 for i in range(200)]
    for modulus in (31, 65537, 2 ** 32 + 15, 2 ** 49 - 1, 2 ** 63 - 25):
        inv = modulus - 2
        data = (U * len(xs))(*reversed(xs))
        table = (U * (4 * 65536))()
        dll.wide_phases(data, data, len(xs), inv, modulus, table)
        assert list(data) == [x * inv % modulus for x in reversed(xs)]
        dll.wide_sort(data, len(xs), modulus, (U * len(xs))(), (U * 65536)())
        assert list(data) == sorted((x * inv % modulus for x in xs))
    cases = [(117, 18000, False), (2 ** 117 + 42, 39449, False),
             (-2 ** 103 + 87, 18137, False), (2 ** 149 + 113, 12000, True)]
    for lo, span, large in cases:
        if large:
            # The injected points force genuine nonempty checks while M*N exceeds 2^64.
            points = [lo + 17, lo + 173, lo + 3809]
            ps = [50021, 50023, 50033, 50047, 50051, 50053]
            rs = [rule(p, [n for n in points]) for p in ps]
            g = [rs[:3], rs[3:]]
            rest = [rule(p, [n for n in points]) for p in (7, 11, 13)]
        else:
            rs = [rule(p, [j for j in range(p) if (j * j + 4 * j + 1) % p < p // 2 + 1]) for p in (7, 11, 13, 17, 19, 23, 29)]
            g = [[rs[0]], [rs[1]]]
            rest = rs[2:]
        for nm in (0, 2):
            s1 = set(range(lo, lo + span + 1))
            s2 = s1.copy()
            s3 = s1.copy()
            for bag, ds in [(s1, list(chain(*g))), (s2, list(chain(*g)) + rest[:nm]), (s3, list(chain(*g)) + rest)]:
                for r in ds:
                    bag.intersection_update((n for n in list(bag) if r.flags[n % r.period]))
            actual, counts = run(dll, lo, lo + span, g, rest[:nm], rest[nm:], False)
            assert actual == sorted(s3) and counts == [len(s1), len(s2), len(s3)]
    # Independently reconstruct the small number of admissible wheel positions
    # across several periods even though the interval includes over 2^64 rows.
    primes = [50021, 50023, 50033, 50047, 50051, 50053]
    rs = [rule(p, [3, 16, 29] if i < 3 else [0, 15, 38, 57, 99]) for i, p in enumerate(primes)]
    modulus = prod(primes)
    lo = -2 ** 119 - 4549
    hi = lo + 3 * modulus + modulus // 3 + 151
    crt = [modulus // p * pow(modulus // p, -1, p) for p in primes]
    wheel_points = []
    for digits in product(*(r.ids for r in rs)):
        root = sum((x * y for x, y in zip(digits, crt))) % modulus
        start = lo + (root - lo) % modulus
        wheel_points.extend(range(start, hi + 1, modulus))
    extra = [rule(p, [j for j in range(p) if (j * j + 5 * j + 3) % p < p * 4 // 5])
             for p in (7, 11, 13, 17, 19, 23, 29, 31, 37, 41)]
    survivors = [n for n in wheel_points if all((r.flags[n % r.period] for r in extra[:8]))]
    expected = sorted((n for n in survivors if all((r.flags[n % r.period] for r in extra[8:]))))
    assert modulus > 2 ** 80 and expected and any((abs(n - lo) > 2 ** 64 for n in expected))
    for block in (47, 1500000):
        actual, counts = run(dll, lo, hi, [rs[:3], rs[3:]], extra[:8], extra[8:], False, block)
        assert actual == expected and counts == [len(wheel_points), len(survivors), len(expected)]
    print('Wide CRT controls passed.', flush=True)

def check_interval(dll, args):
    columns = (5, 6, 7, 8) if args.pattern == 6 else (3, 5, 7, 8)
    assert 0 < args.lower < args.upper and 0 <= args.part < args.parts
    apply_113 = columns == (5, 6, 7, 8) and args.upper <= 175
    if apply_113 and (not args.plan):
        subprocess.run([sys.executable, '-B', str(ROOT / 'Erdos849ResidueDisks.py')], check=True)
    excluded = {}
    if args.mixed:
        assert columns == (5, 6, 7, 8) and args.upper <= 170
        from Erdos849MixedDisks import exclusions
        allowed = exclusions()
        for specification in args.mixed:
            prime, values = specification.split('=')
            p = int(prime)
            values = {int(v) for v in values.split(',')}
            assert p not in excluded and values <= allowed[p]
            excluded[p] = values
    if args.required_53:
        assert columns == (5, 6, 7, 8) and args.lower >= 146 and (args.upper <= 170)
        subprocess.run([sys.executable, '-B', str(ROOT / 'Erdos849RequiredPrime.py')], check=True)
        excluded[53] = set(range(1, 53))
    if args.first_divisors:
        assert columns == (3, 5, 7, 8) and 137 <= args.lower < args.upper <= 185
        if not args.plan:
            for verifier in ('Erdos849ThirteenFactor.py', 'Erdos849First107.py'):
                subprocess.run([sys.executable, '-B', str(ROOT / verifier)], check=True)
        for prime in (13, 107):
            excluded[prime] = set(range(1, prime))
    opts = get_rules(columns, apply_113, excluded)
    choose = optimize_groups if args.optimize else pick
    groups = choose(opts, [args.left, args.right])
    masks, tail = partitions(opts, groups, args.mib, args.right_block)
    low, height = (10 ** args.lower, 10 ** args.upper)
    first, last = (max_row(low, 8) + 1, max_row(height, 8))
    assert comb(first - 1, 8) <= low < comb(first, 8) and comb(last, 8) <= height < comb(last + 1, 8)
    width = last - first + 1
    lo = first + args.part * width // args.parts
    hi = first + (args.part + 1) * width // args.parts - 1
    estimate = (hi - lo + 1) * prod((r.density for r in chain(*groups)))
    print('rows', lo, hi, 'expected joins', format(estimate, '.3g'), 'wheels', [[r.period for r in g] for g in groups], flush=True)
    if args.plan:
        return
    actual, _ = run(dll, lo, hi, groups, masks, tail, block=args.right_block)
    for n in actual:
        a = comb(n, 8)
        assert any((comb(max_row(a, j), j) != a for j in columns[:-1])), (n, a)
    print('No simultaneous coefficients.', flush=True)

def main():
    if not __debug__:
        raise RuntimeError('Run with assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cc', help='C compiler, defaults to clang or cc from PATH')
    parser.add_argument('--pattern', type=int, choices=[3, 6], default=6)
    parser.add_argument('--lower', type=int, default=146)
    parser.add_argument('--upper', type=int, default=150)
    parser.add_argument('--parts', type=int, default=1)
    parser.add_argument('--part', type=int, default=0)
    parser.add_argument('--controls', action='store_true')
    parser.add_argument('--plan', action='store_true')
    parser.add_argument('--left', type=int, default=7000000)
    parser.add_argument('--right', type=int, default=1100000)
    parser.add_argument('--mib', type=int, default=180)
    parser.add_argument('--right-block', type=int, default=1500000)
    parser.add_argument('--optimize', action='store_true')
    parser.add_argument('--mixed', nargs='*', metavar='P=V,V', help='Checked residue exclusions for the second pattern')
    parser.add_argument('--required-53', action='store_true')
    parser.add_argument('--first-divisors', action='store_true',
                        help='Replay the first-pattern certificates forcing 13 and 107 to divide the coefficient')
    args = parser.parse_args()
    cc = args.cc or shutil.which('clang') or shutil.which('cc')
    if not cc:
        parser.error('Supply an installed C compiler via --cc.')
    with TemporaryDirectory() as directory:
        dll = init(cc, directory)
        try:
            controls(dll)
            if not args.controls:
                check_interval(dll, args)
        finally:
            if os.name == 'nt':
                import _ctypes
                _ctypes.FreeLibrary(dll._handle)
if __name__ == '__main__':
    main()
