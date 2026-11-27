"""Search the four-proper-column patterns whose largest column is 8 or 9.

Usage: python -u Erdos849Wheel.py --upper 80
The endpoints are 10^64 (excluded) and 10^upper (included). Combine with
an independent argument for larger columns to infer a multiplicity bound.
"""

from argparse import ArgumentParser
from functools import cache
from itertools import combinations
from math import comb, isqrt
from time import perf_counter


# Theorem 2.2 of Blokhuis, Brouwer and de Weger, arXiv:1707.06893,
# classifies all collisions on these pairs. Their listed exceptions are below
# this interval. The Fibonacci family has no collision on these fixed pairs.
FORBIDDEN = {(2, 3), (2, 4), (2, 5), (2, 6), (2, 8),
             (3, 4), (3, 6), (4, 6), (4, 8)}
PRIMES = [p for p in range(11, 1100)
          if all(p % d for d in range(2, isqrt(p) + 1))]
BLOCK = 1 << 18


def max_row(limit, k):
    lo, hi = k, k << ((limit.bit_length() + k - 1) // k)
    while hi - lo > 1:
        n = (hi + lo) // 2
        if comb(n, k) <= limit:
            lo = n
        else:
            hi = n
    assert comb(lo, k) <= limit < comb(hi, k)
    return lo


@cache
def values(p, k):
    return tuple(comb(n, k) % p for n in range(p))


def allowed_moduli(l, cols):
    # Since k! and l! are units mod p, evaluating each polynomial on residues
    # 0..p-1 covers all possible rows, including rows many periods away.
    out = []
    for p in PRIMES:
        if p <= l:
            continue
        common = set.intersection(*(set(values(p, k)) for k in cols))
        allowed = [i for i, v in enumerate(values(p, l)) if v in common]
        out.append((p, allowed))
    return sorted(out, key=lambda item: len(item[1]) / item[0])


def wheel_residues(moduli):
    # Extending from modulus W to W*p gives exactly one row class for each
    # old/new residue pair, because the primes are distinct.
    w, classes = 1, [0]
    for p, allowed in moduli:
        inverse = pow(w, -1, p)
        classes = [r + w * ((v - r) * inverse % p)
                   for r in classes for v in allowed]
        w *= p
    return w, classes


def periodic_mask(p, allowed, w, horizon, block_size):
    # m=w*b+r. Set s=r/w mod p. The permitted values of b+s mod p are
    # precisely allowed/w. The bitmap repeats every p *bytes*, i.e. 8p bits.
    inv = pow(w, -1, p)
    scaled = {v * inv % p for v in allowed}
    bitmap = bytearray(p)
    for i in range(8*p):
        if i % p in scaled:
            bitmap[i // 8] |= 1 << (i % 8)
    repeats = (min(block_size, horizon) + 8*p - 1) // (8*p) + 2
    return p, inv, pow(8, -1, p), memoryview(bitmap * repeats)


def survivors(first, last, moduli, block_size=BLOCK):
    # Small primes limit the number of CRT classes. Among the small ones choose
    # low image densities. Every threshold below affects speed only.
    wheel = [item for item in moduli if item[0] <= 307][:3]
    w, classes = wheel_residues(wheel)
    wheel_primes = {p for p, _ in wheel}
    rest = [(p, rows) for p, rows in moduli if p not in wheel_primes]
    horizon = (last-first) // w + 2
    bit_tests = [periodic_mask(p, rows, w, horizon, block_size) for p, rows in rest[:22]]
    tail_tests = [(p, frozenset(rows)) for p, rows in rest]
    for r in classes:
        lo = (first - r + w - 1) // w
        limit = (last - r) // w + 1
        for base in range(lo, limit, block_size):
            size = min(block_size, limit - base)
            bits = (1 << size) - 1
            byte_len = (size + 7) // 8
            for p, inv, inv8, template in bit_tests:
                # Bit zero of template byte j represents b+s = 8*j mod p.
                start = ((base + inv*r) * inv8) % p
                bits &= int.from_bytes(template[start:start + byte_len], 'little')
                if not bits or bits.bit_count() <= 3:
                    break
            while bits:
                bit = bits & -bits
                bits ^= bit
                m = w * (base + bit.bit_length() - 1) + r
                if all(m % p in allowed for p, allowed in tail_tests):
                    yield m


def search(lower, upper, l, cols):
    first = max(2*l, max_row(lower, l) + 1)
    last = max_row(upper, l)
    if first > last:
        return 0, []
    matches, checked = [], 0
    for m in survivors(first, last, allowed_moduli(l, cols)):
        checked += 1
        target = comb(m, l)
        rows = [max_row(target, k) for k in cols]
        if all(n >= 2*k and comb(n, k) == target for n, k in zip(rows, cols)):
            matches.append((m, tuple(rows), target))
    return checked, matches


def check_wheel():
    # Check positive and negative modular outcomes, rotated byte offsets, short
    # final blocks, and an interval that starts far from zero, by direct testing.
    first, last = 10**11 + 54321, 10**11 + 550000
    l, cols = 8, (3, 5, 7)
    small = [(p, allowed) for p, allowed in allowed_moduli(l, cols) if p <= 41]
    images = {p: [set(values(p, k)) for k in cols] for p, _ in small}
    expected = set()
    for m in range(first, last + 1):
        v = comb(m, l)
        if all(all(v % p in image for image in group) for p, group in images.items()):
            expected.add(m)
    computed = list(survivors(first, last, small, block_size=13))
    assert 0 < len(expected) < last - first
    assert len(computed) == len(set(computed)) and set(computed) == expected


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--upper', type=int, default=80)
    parser.add_argument('--largest', type=int, choices=(8, 9), nargs='+', default=[8, 9])
    args = parser.parse_args()
    assert 64 < args.upper <= 100
    check_wheel()
    assert search(2999, 3003, 6, (2, 5))[1] == [(14, (78, 15), 3003)]
    assert search(3003, 3020, 6, (2, 5))[1] == []
    for l in args.largest:
        for cols in combinations(range(2, l), 3):
            if any(pair in FORBIDDEN for pair in combinations(cols + (l,), 2)):
                continue
            start = perf_counter()
            checked, matches = search(10**64, 10**args.upper, l, cols)
            print(f"{cols + (l,)}  exact checks {checked}  matches {matches}  "
                  f"{perf_counter() - start:.2f} s", flush=True)
