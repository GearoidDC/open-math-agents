"""Exercise the exact displacement inequalities on Pascal collisions and Lind pairs."""

from collections import defaultdict
from math import comb


def verify_pair(n, k, m, l):
    assert n < m and 1 <= k <= n // 2 and 1 <= l <= m // 2
    assert comb(n, k) == comb(m, l) and l < k
    tests = 0
    matches = []
    for r in range(l + 1):
        for s in range(n - k + 1):
            h = r + s
            if not h:
                continue
            first, second = comb(n - h, k - r), comb(m - h, l - r)
            if h*k <= r*(n+1):
                assert first > second
            if r*(m+1) <= h*l:
                assert first < second
            if first == second:
                assert h*l < r*(m+1) and r*(n+1) < h*k
                if first > 1:
                    matches.append((h, r, first))
            tests += 1
    return tests, matches


def main():
    rows = defaultdict(list)
    for n in range(2, 251):
        for k in range(1, n//2 + 1):
            rows[comb(n, k)].append((n, k))
    pairs = tests = matches = 0
    for positions in rows.values():
        for i, (n, k) in enumerate(positions):
            for m, l in positions[i+1:]:
                count, tied = verify_pair(n, k, m, l)
                pairs += 1
                tests += count
                matches += len(tied)
    # The second adjacent Lind tie maps to the first, witnessing sharpness.
    # The two pairs are (103,40),(104,39) and (14,6),(15,5).
    _, tied = verify_pair(103, 40, 104, 39)
    assert (89, 34, 3003) in tied
    print(f"Rows through 250: {pairs} ordered ties, {tests} admissible translations, "
          f"{matches} common descendant pairs with value >1.")
    print("Depth 89, column shift 34 maps the Lind tie of rows 103–104 to 3003 in rows 14–15.")


if __name__ == "__main__":
    main()
