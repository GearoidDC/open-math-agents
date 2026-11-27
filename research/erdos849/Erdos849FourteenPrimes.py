"""Verify the fourteen-prime restriction on five-row binomial coefficients.

Checks the column graph, the exceptional rows between 10^100 and 10^390,
and the size-uniform cofactor inequalities above that interval.
"""

from itertools import combinations
from math import comb, factorial, isqrt

from Erdos849SingletonCertificate import (
    check, factorial_divisors, floor_root, minimum_product, required_cofactors,
)


LOW = 10**100
HIGH = 10**390
CAP = 13
CLASSIFIED = {(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,6),(4,6),(4,8)}


def classify(j, d):
    """Describe what a collision on this edge must have in the larger column."""
    if (j,d) in CLASSIFIED:
        return "excluded"
    if d > CAP:
        return "empty"
    if d >= 2*j:
        return None
    _, rows = required_cofactors(j,d,LOW)
    target = factorial(d)
    term = floor_root(target*LOW,d)-d+1
    general_exclusion = True
    for empty in range(d+1):
        if term**empty > target:
            break
        singles = max(0, 2*(d-empty)-CAP)
        if term**empty * minimum_product(rows,singles) <= target:
            general_exclusion = False
            break
    if general_exclusion:
        return "excluded"
    singles = max(0,2*d-CAP)
    if minimum_product([[r[-1]] for r in rows],singles) > target:
        return "small or empty"
    return None


def graph():
    # The row bound with t=15 is uniform for all a>=LOW: C(n,15)/n^13
    # increases for n>=15, and a<=n^13 forces n>=this floor root.
    N = floor_root(LOW,CAP)
    assert N >= 30 and comb(N,15) > N**CAP
    edges = {(j,d): classify(j,d) for d in range(3,15) for j in range(2,d)}
    tests = {}
    patterns = 0
    for pattern in combinations(range(2,15),4):
        patterns += 1
        choices = list(combinations(pattern,2))
        if any(edges[e] == "excluded" for e in choices):
            continue
        choices = [e for e in choices if edges[e] in ("empty","small or empty")]
        assert choices, f"uncovered column pattern {pattern}"
        j,d = min(choices, key=lambda e: (edges[e] != "empty",e[1],-e[0]))
        tests.setdefault(d,{})[j] = edges[j,d]
    # These three groups are the short coloring proof used in Lean.
    # Verify every numerical input of the middle-range Lean theorem explicitly.
    for group in ((5,7,8),range(9,15)):
        for j,d in combinations(group,2):
            assert edges[j,d] == "excluded" or j in tests.get(d,{}), (j,d)
    return patterns,tests


def coefficient_filter(d, columns):
    """For n mod p, return the bitmask of still-possible smaller columns."""
    tables = []
    for p in range(d+1,607):
        if any(p%q==0 for q in range(2,isqrt(p)+1)):
            continue
        images = {j:{comb(u,j)%p for u in range(p)} for j in columns}
        table = []
        for u in range(p):
            v = comb(u,d)%p
            table.append(sum(1<<j for j in columns if v in images[j]))
        # The expected number of surviving column bits orders the filters.
        score = sum(mask.bit_count() for mask in table)/p
        tables.append((score,p,table))
    return sorted(tables)


def root_rows(d, small, lower, upper):
    """Enumerate all possible n-s for an empty or a small-prime singleton host."""
    centers = set()
    divisors = factorial_divisors(d)
    for b in divisors:
        if lower-d+1 <= b <= upper:
            centers.add(b)
    if small:
        for p in (2,3,5,7,11,13):
            if p>d:
                continue
            P = p
            while P<=upper:
                for b in divisors:
                    center = b*P
                    if center>upper:
                        break
                    if center>=lower-d+1:
                        centers.add(center)
                P *= p
    return centers


def check_rows(d, edges, low=LOW, high=HIGH):
    columns = sorted(edges)
    lower = floor_root(factorial(d)*low,d)
    upper = floor_root(factorial(d)*high,d)+d
    centers = root_rows(d,"small or empty" in edges.values(),lower,upper)
    tables = coefficient_filter(d,columns)
    start = sum(1<<j for j in columns)
    rows = exact = 0
    for center in sorted(centers):
        for n in range(max(lower,center),min(upper,center+d-1)+1):
            rows += 1
            possible = start
            for _,p,table in tables:
                possible &= table[n%p]
                if not possible:
                    break
            if possible:
                value = comb(n,d)
                if low<=value<=high:
                    for j in columns:
                        if not possible & (1<<j):
                            continue
                        exact += 1
                        # Any exact row is within j integers of the real root.
                        root = floor_root(factorial(j)*value,j)
                        assert all(comb(m,j)!=value for m in range(root,root+j+1)), (n,d,j)
    print(f"d={d}, smaller columns {columns}: {rows} candidate rows, {exact} exact tests",flush=True)
    return rows,exact


def main():
    assert not check(CAP,390), "large-value cofactor bound failed"
    patterns,tests = graph()
    print(f"Covered all {patterns} four-column subsets. Finite tests: {tests}",flush=True)
    counts = [check_rows(d,tests[d]) for d in sorted(tests)]
    print(f"Excluded all exceptional rows: {sum(t[0] for t in counts)} candidates "
          f"with repetitions, {sum(t[1] for t in counts)} exact tests.")


if __name__ == "__main__":
    main()
