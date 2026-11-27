"""Remaining finite cases from Erdos849PrimePowerRow.txt (columns 7 and 8)."""

from math import comb, factorial


def valuation(n, p):
    out = 0
    while n % p == 0:
        n //= p
        out += 1
    return out


def row(a, k):
    lo, hi = 2 * k - 1, 2 * k
    while comb(hi, k) < a:
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if comb(mid, k) < a:
            lo = mid
        else:
            hi = mid
    return hi if comb(hi, k) == a else None


def main():
    assert 4096**6 > 980**7
    small_b, small_loss = [], []
    for p in (2, 3, 5, 7):
        b = p ** valuation(factorial(8), p)
        small_b.append(b)
        small_loss.append(b * p ** valuation(factorial(7) * factorial(6), p))
    assert max(small_b) == 128 and max(small_loss) == 32768
    assert 980 * 128 * 32768 < 10**12
    assert 2048 * 19**7 < 10**14
    assert all((7 * comb(6, r)) % 8 for r in range(7))
    candidates = set(range(16, 4096 + 7))
    for p in (2, 3, 5, 7):
        P = p
        while P < 10**14:
            candidates.update(P + s for s in range(8) if P + s >= 16)
            P *= p
    matches = [(n, m) for n in sorted(candidates)
               if (m := row(comb(n, 8), 7)) is not None]
    print('candidate eighth-column rows', len(candidates), 'matches', matches)
    assert not matches

    assert (64 - 7)**8 > 8 * (64 + 6)**7
    assert 32**8 * factorial(8) * 2**7 < 10**20
    for k in (3, 5, 7):
        small_n = [(n, row(comb(n, 8), k)) for n in range(16, 64)]
        assert all(m is None for n, m in small_n)
        candidates = set()
        for p in (2, 3, 5, 7):
            if p > k:
                continue
            assert p**valuation(factorial(k), p) <= 16
            P = p
            while P < 10**20:
                candidates.update(P + r for r in range(k) if P + r >= 2 * k)
                P *= p
        matches = [(m, n) for m in sorted(candidates)
                   if (n := row(comb(m, k), 8)) is not None]
        print('column', k, 'small-prime candidate rows', len(candidates),
              'plus 48 eighth-column rows; matches', matches)
        assert not matches


if __name__ == '__main__':
    main()
