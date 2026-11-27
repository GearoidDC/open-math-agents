"""Generate the finite obligations for a five-row value with at most 15 primes."""

from functools import cache
from itertools import combinations
from math import comb
from Erdos849FifteenPrimes import classify, graph
from Erdos849FourteenPrimes import check_rows
from Erdos849SingletonCertificate import floor_root


CAP = 15
LOW = 100
HIGH = 500


@cache
def edge(j,d,k):
    return classify(j,d,10**k,CAP)


def select(pattern,k):
    pairs = [(e,edge(*e,k)) for e in combinations(pattern,2)]
    valid = [(e,status) for e,status in pairs if status]
    if not valid:
        return None
    cost = {"excluded":0,"empty":1,"small or empty":2}
    return min(valid,key=lambda item:(cost[item[1]],item[0][1],-item[0][0]))


def plan():
    upper,patterns,obligations = graph(10**HIGH,CAP)
    assert upper == 16 and patterns == 1001 and not obligations
    N = floor_root(10**LOW,CAP)
    assert N>=36 and comb(N,18)>N**CAP
    finite = {}
    direct = {}
    for pattern in combinations(range(2,18),4):
        boundary = LOW
        chosen = select(pattern,boundary)
        if chosen is None:
            left,right = LOW,HIGH
            while right>left+1:
                mid = (left+right)//2
                if select(pattern,mid) is not None:
                    right = mid
                else:
                    left = mid
            boundary = right
            chosen = select(pattern,boundary)
            assert chosen is not None
            # Nothing is presumed about smaller cutoffs: sieve the entire gap.
            direct[pattern] = boundary
        (j,d),what = chosen
        if what != "excluded":
            by_col = finite.setdefault(d,{})
            # We may safely enlarge any lower endpoint back to a googol.
            if what == "small or empty" or j not in by_col:
                by_col[j] = what
    return finite,direct


if __name__ == "__main__":
    tests,patterns = plan()
    print(f"Finite host obligations {tests}",flush=True)
    for d,cols in sorted(tests.items()):
        check_rows(d,cols,10**LOW,10**HIGH)
    print("Direct simultaneous-column intervals:")
    for p,k in sorted(patterns.items()):
        print(p,k)
