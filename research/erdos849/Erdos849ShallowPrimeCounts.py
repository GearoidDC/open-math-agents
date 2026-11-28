"""Height-dependent lower bounds for the prime count in either four-column pattern."""

from functools import cache
from itertools import combinations
from math import factorial, prod
from Erdos849PatternThree import host_loss, root, valuation


@cache
def loss(k, subset):
    if k == 8:
        return prod(host_loss(subset, p) for p in (2, 3, 5, 7))

    # Remove one maximal term, keeping the first in a tie. At a zero residue
    # further lifts increase its valuation and the assigned exponent together.
    result = 1
    for p in (2, 3, 5, 7):
        modulus = p
        while modulus <= k:
            modulus *= p
        maximum = 0
        for n in range(modulus):
            vals = [valuation((n-i) % modulus or modulus, p) for i in range(k)]
            host = vals.index(max(vals))
            exponent = sum(vals)-valuation(factorial(k), p)
            assert 0 <= exponent <= vals[host]
            excess = sum(vals[i] for i in subset)
            if host in subset:
                excess -= exponent
                if exponent or n == host:
                    excess += valuation(420, p)
            maximum = max(maximum, excess)
        result *= p**maximum
    return result


def verify(k, minimum, decade, target):
    # Test distributions of target-1 primes. A smaller distribution could
    # be padded to this size without violating any of the lower bounds.
    budget = target-1
    smallest_term = root(k, decade) - k + 1
    factor = 35519**36 * 10**(decade-128)
    constraints = [[] for _ in range(k+1)]
    for size in range(1,k+1):
        real_lower = smallest_term**(36*size)
        for subset in combinations(range(k), size):
            cofactor = loss(k, subset)**36
            needed = minimum*size
            for count in range(needed, min(budget, 36*size//k)+1):
                if real_lower > cofactor*factor**count:
                    needed = count+1
            constraints[subset[-1]+1].append((subset, needed))

    def possible(prefix, spare):
        if any(sum(prefix[i] for i in subset)<needed
               for subset,needed in constraints[len(prefix)]):
            return False
        if len(prefix)==k:
            return spare==0
        return any(possible((*prefix, minimum+extra), spare-extra)
                   for extra in range(spare+1))

    assert budget >= minimum*k
    assert not possible((), budget-minimum*k)
    print(f"At or above 10^{decade}: at least {target} distinct prime divisors.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    for decade,target in [(350,36), (370,37), (400,38), (456,39), (611,40)]:
        verify(8, 4, decade, target)
    for decade,target in [(1850,41), (2350,42)]:
        verify(7, 5, decade, target)
