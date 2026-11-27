"""Verify the numerical and graph steps of the fifteen-prime restriction.

The column (7,14) argument is in Erdos849DoubleColumn.txt. All other
non-published edge tests are specified here and in the imported Python files.
"""

from functools import cache
from itertools import combinations
from math import comb, factorial
from Erdos849FourteenPrimes import CLASSIFIED, check_rows
from Erdos849SingletonCertificate import floor_root, minimum_product, required_cofactors


CAP = 14
LOW, HIGH = 10**100, 10**500


@cache
def transfer_cost(j,d,S,X):
    """Minimum product of the singletons' cofactors, grouping their prime
    powers according to which of the j terms in the other row they divide."""
    L = floor_root(factorial(d)*X,d)-d+1
    U = floor_root(factorial(j)*X,j)+j
    costs = [1 if h*j < d else max(1,(L**h+U-1)//U) for h in range(S+1)]
    # Enumerate every distribution, including empty bins, using integer DP.
    best = [1] + [None]*S
    for _ in range(j):
        best = [min(best[t]*costs[i-t] for t in range(i+1) if best[t] is not None)
                for i in range(S+1)]
    return best[S]


def classify(j,d,X,cap=CAP):
    """Return an obstruction that is necessary for this pair to occur."""
    if (j,d) in CLASSIFIED:
        return "excluded"
    L = floor_root(factorial(d)*X,d)-d+1
    target = factorial(d)
    if d>cap or ((j,d)==(7,14) and cap<=14):
        return "excluded" if L>target else "empty"
    rows = required_cofactors(j,d,X)[1] if d<2*j else None
    possible = []
    for empty in range(d+1):
        if L**empty>target:
            break
        S = max(0,2*(d-empty)-cap)
        group = transfer_cost(j,d,S,X)
        singleton = minimum_product(rows,S) if rows is not None else 1
        if L**empty*max(group,singleton)>target:
            continue
        if empty:
            possible.append("empty")
        elif rows and minimum_product([[r[-1]] for r in rows],S)>target:
            possible.append("small or empty")
        else:
            return None
    if not possible:
        return "excluded"
    return "small or empty" if "small or empty" in possible else "empty"


def graph(X,cap=CAP):
    N = floor_root(X,cap)
    cutoff = next(t for t in range(cap+1,20) if N>=2*t and comb(N,t)>N**cap)
    edges = {(j,d):classify(j,d,X,cap) for d in range(3,cutoff) for j in range(2,d)}
    tests = {}
    patterns = 0
    for pattern in combinations(range(2,cutoff),4):
        patterns += 1
        pairs = list(combinations(pattern,2))
        if any(edges[e]=="excluded" for e in pairs):
            continue
        candidates = [e for e in pairs if edges[e]]
        assert candidates, f"unresolved {pattern} at cutoff {cutoff}"
        j,d = min(candidates,key=lambda e:(edges[e]!="empty",e[1],-e[0]))
        tests.setdefault(d,{})[j] = edges[j,d]
    return cutoff,patterns,tests


def main():
    high_cut,high_patterns,upper = graph(HIGH)
    assert not upper, "unbounded region has finite-search obligations"
    print(f"Large range: {high_patterns} patterns excluded, d<{high_cut}")
    low_cut,low_patterns,tests = graph(LOW)
    print(f"Middle range: {low_patterns} patterns, d<{low_cut}, exceptions {tests}",flush=True)
    counts = [check_rows(d,edges,LOW,HIGH) for d,edges in sorted(tests.items())]
    print(f"Examined {sum(r for r,_ in counts)} candidate rows and "
          f"{sum(e for _,e in counts)} exact binomial inversions.")


if __name__ == "__main__":
    main()
